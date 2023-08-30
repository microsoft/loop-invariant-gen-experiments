import argparse
import json
import re
import sys
import traceback

from lark import Lark, Token, Transformer

"""
Measuring:

1. Number of variables
2. Number of constants
3. Number of unary operators
4. Number of binary operators
5. Number of ternary operators

"""

expression_grammar = r"""
    expression: VARIABLE 
        | NUMBER 
        | TRUE 
        | FALSE
        | unary_op expression 
        | expression (bin_op expression)+ 
        | LPAREN expression RPAREN 
        | VALID LPAREN expression RPAREN
        | VARIABLE LSQUARE expression RSQUARE
        | expression TERNOP expression COLON expression 
        | AT LPAREN VARIABLE COMMA location RPAREN
        | FORALL TYPE VARIABLE SEMICOLON expression

    !location: "Pre" | "Here" | "Old" | "Post" | "LoopEntry" | "LoopCurrent"

    !unary_op : "+" | "-" | "!" | "&"

    !bin_op : "+" | "-" | "*" | "/" | "%" | "^^" | "<<" | ">>" | "&" | "|" | "-->" | "<-->" | "^" | "==" | "!=" | "<" | ">" | "<=" | ">="
        | "&&" | "||" | "^^" | "==>" | "<==>"

    COMMA : ","
    AT: "\\at"

    TRUE : "\\true"
    FALSE: "\\false"
    FORALL: "\\forall"
    VALID: "\\valid"
    TYPE: "int" | "float" | "double" | "char" | "bool" | "void" | "integer" | "boolean"
    LPAREN: "("
    RPAREN: ")"
    LSQUARE: "["
    RSQUARE: "]"
    TERNOP: "?"
    COLON: ":"
    SEMICOLON: ";"

    %import common.NUMBER
    %extend NUMBER: /0x\w+/
    
    %import common.CNAME -> VARIABLE

    %import common.WS
    %ignore WS
"""

class ExpTransformer(Transformer):
    def __init__(self):
        self.variables = {}
        self.constants = {}
        self.num_unary_ops = 0
        self.num_binary_ops = 0
        self.num_ternary_ops = 0
        self.ordering_exps = 0
        self.num_forall = 0
        self.num_valid = 0

    def expression(self, args):
        if len(args) == 5 and args[1] == "?":
            self.num_ternary_ops += 1
        elif len(args) == 5 and args[1] in ["<", ">", "<=", ">="]:
            self.ordering_exps += 1
        elif len(args) == 2:
            self.num_unary_ops += 1
        elif len(args) >= 3 and len(args) % 2 == 1 and args[0] != "(" and args[2] != ")":
            self.num_binary_ops += 1

        string = " ".join(args)
        return string
    
    def bin_op(self, args):
        string = " ".join(args)
        return string
    
    def unary_op(self, args):
        string = " ".join(args)
        return string
    
    def FORALL(self, args):
        self.num_forall += 1
        return args
    
    def VALID(self, args):
        self.num_valid += 1
        return args

    def VARIABLE(self, args):
        string = str(args)
        self.variables[string] = True
        return string
    
    def NUMBER(self, args):
        string = str(args)
        self.constants[string] = True
        return args
    
    def add_stats(self, ast):
        self.transform(ast)

    def get_stats(self):
        res_json = {
            "num_variables": len(self.variables),
            "num_constants": len(self.constants),
            "num_unary_ops": self.num_unary_ops,
            "num_binary_ops": self.num_binary_ops,
            "num_ternary_ops": self.num_ternary_ops,
            "num_forall": self.num_forall,
            "num_valid": self.num_valid
        }
        return res_json
    
    def __default_token__(self, token):
        return str(token)

predicate_grammar = r"""
    term: VAR | NUMBER | unary_op term | term bin_op term | LPAREN term RPAREN | term TERNOP term COLON term | AT LPAREN VAR COMMA location RPAREN

    !location: "Pre" | "Here" | "Old" | "Post" | "LoopEntry" | "LoopCurrent"

    !unary_op : "+" | "-" | "!" 

    !bin_op : "+" | "-" | "*" | "/" | "%" | "^^" | "<<" | ">>" | "&" | "|" | "-->" | "<-->" | "^" | rel_op

    pred: TRUE | FALSE
        | LPAREN pred RPAREN
        | term (rel_op term)+
        | pred LAND pred
        | pred LOR pred
        | pred LIMPL pred
        | pred LBIIMPL pred
        | LNOT pred
        | pred LXOR pred
        | term TERNOP pred COLON pred
        | pred TERNOP pred COLON pred

    !rel_op : "==" | "!=" | "<" | ">" | "<=" | ">="

    VAR: /[a-zA-Z_][a-zA-Z0-9_]*/
    NUMBER: /[0-9]+(\.[0-9]+)*/
    COMMA : ","
    AT: "\\at"

    TRUE : "\\true"
    FALSE: "\\false"
    LPAREN: "("
    RPAREN: ")"
    LAND: "&&"
    LOR: "||"
    LIMPL: "==>"
    LBIIMPL: "<==>"
    LNOT: "!"
    LXOR: "^^"
    TERNOP: "?"
    COLON: ":"
    SEMICOLON: ";"
    FORALL: "\\forall"
    EXISTS: "\\exists"

    %import common.WS
    %ignore WS
"""


class PredicateTransformer(Transformer):
    def __init__(self):
        self.clauses = []
        self.terms = []
        self.variables = {}
        self.constants = {}
        self.num_unary = 0
        self.num_binary = 0
        self.num_ternary = 0

    def pred(self, args):
        if len(args) == 5 and args[1] == "?":
            self.num_ternary += 1
        if len(args) == 2 and args[0] == "!" and args[1] in self.clauses:
            self.clauses.remove(args[1])
        if (
            len(args) == 3
            and args[0] == "("
            and args[2] == ")"
            and args[1] in self.clauses
        ):
            self.clauses.remove(args[1])

        string = " ".join(args)
        if not any([clause in string for clause in self.clauses]):
            self.clauses.append(string)
        return string

    def term(self, args):
        if len(args) == 5 and args[1] == "?":
            self.num_ternary += 1
        string = " ".join(args)
        self.terms.append(string)
        return string

    def VAR(self, args):
        string = str(args)
        self.variables[string] = True
        return string

    def NUMBER(self, args):
        string = str(args)
        self.constants[string] = True
        return args

    def bin_op(self, args):
        self.num_binary += 1
        return args[0]

    def unary_op(self, args):
        self.num_unary += 1
        return args[0]

    def rel_op(self, args):
        return args[0]

    def location(self, args):
        return args[0]

    def add_stats(self, ast):
        self.transform(ast)

    def compute_clause_size(self, clause):
        parser = Lark(predicate_grammar, parser="lalr", start="pred")
        ast = parser.parse(clause)

        def rec_compute_clause_size(ast):
            if isinstance(ast, Token):
                return 1
            else:
                return sum([rec_compute_clause_size(child) for child in ast.children])

        return rec_compute_clause_size(ast)

    def get_stats(self):
        clause_sizes = []
        biggest_clause = ""
        biggest_clause_size = 0
        for clause in self.clauses:
            clause_size = self.compute_clause_size(clause)
            if clause_size > biggest_clause_size:
                biggest_clause = clause
                biggest_clause_size = clause_size
            clause_sizes.append(clause_size)
        res_json = {
            "num_clauses": len(self.clauses),
            "biggest_clause": biggest_clause,
            "biggest_clause_size": biggest_clause_size,
            "avg_clause_size": sum(clause_sizes) / len(self.clauses),
            "num_variables": len(self.variables),
            "num_constants": len(self.constants),
            "num_unary_ops": self.num_unary,
            "num_binary_ops": self.num_binary,
            "num_ternary_ops": self.num_ternary,
        }
        return res_json

    def __default_token__(self, token):
        return str(token)


class InvariantParser:
    def __init__(self):
        self.parser = Lark(expression_grammar, parser="lalr", start="expression")

    def get_invariants(self, text):
        invariants = {}
        candidate_invs = re.findall(r"loop invariant ([\S+]*\s*:)?(.+);", text)
        candidate_invs = [inv[1] for inv in candidate_invs]
        for inv in candidate_invs:
            invariants[inv] = True
        return list(invariants.keys())

    def get_stats(self, text):
        transformer = ExpTransformer()
        invariants = self.get_invariants(text)
        for inv in invariants:
            ast = self.parser.parse(inv)
            transformer.add_stats(ast)
        res = transformer.get_stats()
        res["num_conjuncts_in_completion"] = len(invariants)
        return res


def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument("--input-log", type=str, required=True)
    parser.add_argument("--input-log-2", type=str, required=False)
    return parser.parse_args(args)


def main(args):
    args = parse_args(args)
    ip = InvariantParser()
    logs_1 = None
    logs_2 = None
    with open(args.input_log, "r", encoding="utf-8") as f:
        logs_1 = json.load(f)
    logs_1 = logs_1["logs"]
    if args.input_log_2:
        with open(args.input_log_2, "r", encoding="utf-8") as f:
            logs_2 = json.load(f)
        logs_2 = logs_2["logs"]

    output_logs = []
    for i, log in enumerate(logs_1):
        if "completions" not in log:
            continue
        assert log["file"] == logs_2[i]["file"]
        for j, completion in enumerate(log["completions"]):
            if completion["success"]:
                invariant = completion["invariants"]
                try:
                    stats = ip.get_stats(invariant)
                    output_logs.append(
                        {
                            "invariant": invariant,
                            "stats": stats,
                            "file": log["file"],
                        }
                    )
                except Exception as e:
                    print(e)
                    output_logs.append(
                        {
                            "invariant": invariant,
                            "stats": None,
                            "file": log["file"],
                            "exception": traceback.format_exc(),
                        }
                    )

        for k, completion in enumerate(logs_2[i]["completions"]):
            if completion["success"]:
                invariant = completion["invariants"]
                try:
                    stats = ip.get_stats(invariant)
                    output_logs.append(
                        {
                            "invariant": invariant,
                            "stats": stats,
                            "file": log["file"],
                        }
                    )
                except Exception as e:
                    print(e)
                    output_logs.append(
                        {
                            "invariant": invariant,
                            "stats": None,
                            "file": log["file"],
                            "exception": traceback.format_exc(),
                        }
                    )

    output_log_file = args.input_log + ".invariant.stats.json"
    with open(output_log_file, "w", encoding="utf-8") as f:
        json.dump({"logs": output_logs}, f, indent=4, ensure_ascii=False)


# if __name__ == "__main__":
#     main(sys.argv[1:])

invariants = "@*/\n  loop invariant x1 >= 0;\n  loop invariant x2 >= 0;\n  loop invariant x3 >= 0;\n  loop invariant d1 == 1;\n  loop invariant d2 == 1;\n  loop invariant d3 == 1;\n  loop invariant \\valid(&c1);\n  loop invariant \\valid(&c2);\n/*@*/"
ip = InvariantParser()
print(ip.get_stats(invariants))
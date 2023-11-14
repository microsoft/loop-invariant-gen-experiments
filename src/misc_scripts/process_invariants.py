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
        | function LPAREN expression RPAREN
        | VARIABLE LSQUARE expression RSQUARE
        | expression TERNOP expression COLON expression 
        | AT LPAREN expression COMMA location RPAREN
        | FORALL TYPE VARIABLE SEMICOLON expression

    function: VALID | FLOOR

    location: "Pre" | "Here" | "Old" | "Post" | "LoopEntry" | "LoopCurrent"

    unary_op : "+" | "-" | "!" | "&"

    !bin_op : "+" | "-" | "*" | "/" | "%" | "^^" | "<<" | ">>" | "&" | "|" | "-->" | "<-->" | "^" | "==" | "!=" | "<" | ">" | "<=" | ">="
        | "&&" | "||" | "^^" | "==>" | "<==>"

    COMMA : ","
    AT: "\\at"

    TRUE : "\\true"
    FALSE: "\\false"
    FORALL: "\\forall"
    VALID: "\\valid"
    FLOOR: "\\floor"
    TYPE: "int" | "float" | "double" | "char" | "bool" | "void" | "integer" | "boolean"
    LPAREN: "("
    RPAREN: ")"
    LSQUARE: "["
    RSQUARE: "]"
    TERNOP: "?"
    COLON: ":"
    SEMICOLON: ";"

    %import common.NUMBER
    %extend NUMBER: /0x\w+/ | /[0-9]+/ "U" | /[0-9]+/ "u" | /[0-9]+/ "L" | /[0-9]+/ "l" | /[0-9]+/ "F" | /[0-9]+/ "f"
    
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
        self.num_at = 0
        self.num_conjunctions = 0
        self.num_disjunctions = 0
        self.num_implications = 0
        self.bi_implications = 0

    def expression(self, args):
        if len(args) == 3:
            if args[1] == "&&":
                self.num_conjunctions += 1
            elif args[1] == "||":
                self.num_disjunctions += 1
            elif args[1] == "==>":
                self.num_implications += 1
            elif args[1] == "<==>":
                self.bi_implications += 1

        if len(args) == 5 and args[1] == "?":
            self.num_ternary_ops += 1
        elif len(args) == 5 and args[1] in ["<", ">", "<=", ">="]:
            self.ordering_exps += 1
        elif len(args) == 2:
            self.num_unary_ops += 1
        elif (
            len(args) >= 3 and len(args) % 2 == 1 and args[0] != "(" and args[2] != ")"
        ):
            self.num_binary_ops += 1
        return "expression"

    def bin_op(self, args):
        if args[0] == "&&":
            self.num_conjunctions += 1
        elif args[0] == "||":
            self.num_disjunctions += 1
        elif args[0] == "==>":
            self.num_implications += 1
        elif args[0] == "<==>":
            self.bi_implications += 1

        string = " ".join(args)
        return "bin_op"

    def unary_op(self, args):
        string = " ".join(args)
        return "unary_op"

    def FORALL(self, args):
        self.num_forall += 1
        return "Forall "

    def VALID(self, args):
        self.num_valid += 1
        return "Valid "

    def AT(self, args):
        self.num_at += 1
        return "At "

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
            "num_valid": self.num_valid,
            "num_at": self.num_at,
            "num_conjunctions": self.num_conjunctions,
            "num_disjunctions": self.num_disjunctions,
            "num_implications": self.num_implications,
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


if __name__ == "__main__":
    main(sys.argv[1:])

import argparse
import json
import re
import sys
import traceback
import os

from lark import Lark, Token, Transformer

sys.path.append(os.path.dirname(__file__) + "/../")
from frama_c import FramaCChecker, FramaCBenchmark
from llm_utils import Logger

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
        | EXISTS TYPE VARIABLE SEMICOLON expression

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
    EXISTS: "\\exists"
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
        self.num_exists = 0
        self.num_valid = 0
        self.num_at = 0
        self.num_conjunctions = 0
        self.num_disjunctions = 0
        self.num_implications = 0
        self.bi_implications = 0
        self.depth = []

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

    def EXISTS(self, args):
        self.num_exists += 1
        return "Exists "

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

    def get_depth(self, ast):
        if isinstance(ast, Token) or len(ast.children) == 0:
            return 0
        if len(ast.children) == 1:
            return self.get_depth(ast.children[0])
        return 1 + max([self.get_depth(child) for child in ast.children])

    def add_stats(self, ast):
        inv_depth = self.get_depth(ast)
        self.depth.append(inv_depth)
        self.transform(ast)

    def get_stats(self):
        res_json = {
            "num_variables": len(self.variables),
            "num_constants": len(self.constants),
            "num_unary_ops": self.num_unary_ops,
            "num_binary_ops": self.num_binary_ops,
            "num_ternary_ops": self.num_ternary_ops,
            "num_forall": self.num_forall,
            "num_exists": self.num_exists,
            "num_valid": self.num_valid,
            "num_at": self.num_at,
            "num_conjunctions": self.num_conjunctions,
            "num_disjunctions": self.num_disjunctions,
            "num_implications": self.num_implications,
            "depths": self.depth,
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
        invariant_stats = []
        for inv in invariants:
            ast = self.parser.parse(inv)
            transformer = ExpTransformer()
            transformer.add_stats(ast)
            invariant_stats.append({
                "invariant": inv,
                "stats": transformer.get_stats()
            })

        return invariant_stats
        # res = transformer.get_stats()
        # res["num_conjuncts_in_completion"] = len(invariants)
        # return res

log_file = "final_feats_log.json"
log_json = None
with open(log_file, "r", encoding="utf-8") as f:
    log_json = json.load(f)

ip = InvariantParser()
final_log = []
for i, log in enumerate(log_json):
    Logger.log_info(f"[{i+1}/555] Processing {log['file']}")
    if log["invariants"] is None:
        final_log.append({
            "file": log["file"],
            "invariant": log["invariants"],
            "stats": None
        })
        continue
    invariant_stats = ip.get_stats(log["invariants"])
    final_log.append({
        "file": log["file"],
        "invariant": log["invariants"],
        "stats": invariant_stats
    })

with open(log_file + ".final_invariant_stats.json", "w", encoding="utf-8") as f:
    json.dump(final_log, f, indent=4, ensure_ascii=False)

sys.exit(0)

start_index = int(sys.argv[1])
end_index = int(sys.argv[2])

log_file = "loop_invariants_m1_prompt.json"
log_json = None
with open(log_file, "r", encoding="utf-8") as f:
    log_json = json.load(f)

ultimate_disproved = []
ult_logs = None

with open("loop_invariants.json", "r", encoding="utf-8") as f:
    ult_logs = json.load(f)

for key, value in ult_logs.items():
    if value["result"] == "Disproved":
        ultimate_disproved.append(key)

ip = InvariantParser()
fc = FramaCChecker()
fb = FramaCBenchmark()
output_log = []
total_to_do = 0
for i, b in enumerate(log_json["logs"][start_index:end_index]):
    Logger.log_info(f"[{i + 1}/555] Processing {b['file']}")
    if any([completion["success"] for completion in b["completions"]]):
        Logger.log_success(f"[{i + 1}/555] Benchmark has a successful completion")
        success_completions = [
            completion["invariants"]
            for completion in b["completions"]
            if completion["success"]
        ]
        output_log.append(
            {
                "file": b["file"],
                "invariants": success_completions[0],
                "features": ip.get_stats(success_completions[0]),
            }
        )
        continue
    if any([completion["success_after_prune"] for completion in b["completions"]]):
        Logger.log_success(
            f"[{i + 1}/555] Benchmark has a successful completion but needs Houdini"
        )
        success_completion_code = [
            completion["pruned_code"]
            for completion in b["completions"]
            if completion["success_after_prune"]
        ]
        success_completion_code = success_completion_code[0]
        success_invariants = fb.extract_loop_invariants(success_completion_code)
        output_log.append(
            {
                "file": b["file"],
                "invariants": success_invariants,
                "features": ip.get_stats(success_invariants),
            }
        )
        continue
    file_name = b["file"]
    if file_name.startswith("../new_benchmarks/original_benchmarks/"):
        file_name = (
            "../../data/benchmarks/"
            + file_name[len("../new_benchmarks/original_benchmarks/") :]
        )
    elif file_name.startswith("../data/benchmarks/"):
        file_name = "../" + file_name

    if file_name in ultimate_disproved:
        output_log.append(
            {
                "file": b["file"],
                "invariants": None,
                "features": None,
                "reason": "Ultimate disproved",
            }
        )
        continue
    else:
        combined_llm_input = fb.combine_llm_outputs(
            b["benchmark_code"], b["invariants"], features="one_loop_one_method"
        )
        success, pruned_code, num_calls = fc.houdini(
            combined_llm_input, "one_loop_one_method", use_json_dump_for_invariants=True
        )
        if not success:
            Logger.log_error(f"[{i + 1}/555] Benchmark has no inductive invariants")
            output_log.append(
                {
                    "file": b["file"],
                    "invariants": None,
                    "features": None,
                    "reason": "Houdini failed",
                    "pruned_code": pruned_code,
                }
            )
            continue
        success_invariants = fb.extract_loop_invariants(pruned_code)
        Logger.log_success(
            f"[{i + 1}/555] Benchmark has a successful completion after Houdini"
        )
        output_log.append(
            {
                "file": b["file"],
                "invariants": success_invariants,
                "features": ip.get_stats(success_invariants),
            }
        )

with open(log_file + f".features_{start_index}_{end_index}.json", "w", encoding="utf-8") as f:
    json.dump({"logs": output_log}, f, indent=4, ensure_ascii=False)


# def parse_args(args):
#     parser = argparse.ArgumentParser()
#     parser.add_argument("--input-log", type=str, required=True)
#     parser.add_argument("--input-log-2", type=str, required=False)
#     return parser.parse_args(args)


# def main(args):
#     args = parse_args(args)
#     ip = InvariantParser()
#     logs_1 = None
#     logs_2 = None
#     with open(args.input_log, "r", encoding="utf-8") as f:
#         logs_1 = json.load(f)
#     logs_1 = logs_1["logs"]
#     if args.input_log_2:
#         with open(args.input_log_2, "r", encoding="utf-8") as f:
#             logs_2 = json.load(f)
#         logs_2 = logs_2["logs"]

#     output_logs = []
#     for i, log in enumerate(logs_1):
#         if "completions" not in log:
#             continue
#         assert log["file"] == logs_2[i]["file"]
#         for j, completion in enumerate(log["completions"]):
#             if completion["success"]:
#                 invariant = completion["invariants"]
#                 try:
#                     stats = ip.get_stats(invariant)
#                     output_logs.append(
#                         {
#                             "invariant": invariant,
#                             "stats": stats,
#                             "file": log["file"],
#                         }
#                     )
#                 except Exception as e:
#                     print(e)
#                     output_logs.append(
#                         {
#                             "invariant": invariant,
#                             "stats": None,
#                             "file": log["file"],
#                             "exception": traceback.format_exc(),
#                         }
#                     )

#         for k, completion in enumerate(logs_2[i]["completions"]):
#             if completion["success"]:
#                 invariant = completion["invariants"]
#                 try:
#                     stats = ip.get_stats(invariant)
#                     output_logs.append(
#                         {
#                             "invariant": invariant,
#                             "stats": stats,
#                             "file": log["file"],
#                         }
#                     )
#                 except Exception as e:
#                     print(e)
#                     output_logs.append(
#                         {
#                             "invariant": invariant,
#                             "stats": None,
#                             "file": log["file"],
#                             "exception": traceback.format_exc(),
#                         }
#                     )

#     output_log_file = args.input_log + ".invariant.stats.json"
#     with open(output_log_file, "w", encoding="utf-8") as f:
#         json.dump({"logs": output_logs}, f, indent=4, ensure_ascii=False)


# if __name__ == "__main__":
#     main(sys.argv[1:])

import argparse
import os
import re
import sys

from tree_sitter import Language, Parser


class Code2InvParser:
    def __init__(self, language_name):
        lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
        self.language = Language(lib_path + "c-tree-sitter.so", language_name)
        self.parser = Parser()
        self.parser.set_language(self.language)

    def get_modified_asserts(self, code):
        ast = self.parse(code)
        qs = self.get_query_string(2)
        f1 = bp.language.query(qs).captures(ast.root_node)

        premise = " ∧ ".join(
            [
                self.strip_matching_brackets(x[0].text.decode("utf-8"))
                for x in f1
                if x[1] == "premise"
            ]
        )
        conclusion = " ∧ ".join(
            [
                self.strip_matching_brackets(x[0].text.decode("utf-8"))
                for x in f1
                if x[1] == "conclusion"
            ]
        )
        post_c = "//@ assert(" + premise + " => " + conclusion + ");"

        return post_c

    def strip_matching_brackets(self, s):
        c = s.strip()
        if c.startswith("(") and c.endswith(")"):
            return self.strip_matching_brackets(c[1:-1])
        return s

    def __get_query_string(self, cur_depth, max_depth):
        if max_depth == 0:
            return """((expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))
            (#eq? @function-name "assert"))"""

        elif cur_depth == 0:
            return """(expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))"""

        elif cur_depth < max_depth:
            return (
                """(if_statement (
                    ((parenthesized_expression) @premise)
                    """
                + self.__get_query_string(cur_depth - 1, max_depth)
                + """
                    ))"""
            )
        elif cur_depth == max_depth:
            return (
                """((if_statement (
                            ((parenthesized_expression) @premise)
                            """
                + self.__get_query_string(cur_depth - 1, max_depth)
                + """
                                ) @outer-if-statement
                        )
                        (#eq? @function-name "assert")
                        )"""
            )

    def get_query_string(self, n):
        return self.__get_query_string(n, n)

    def get_assumes(self, code):
        ast = self.parse(code)
        assumes = self.language.query(
            """((call_expression (identifier) @function-name)
                    (#eq? @function-name "assume"))"""
        ).captures(ast.root_node)
        return [x[0] for x in assumes]

    def parse(self, code):
        return self.parser.parse(bytes(code, "utf8"))


c_program = """
int main() {
  // variable declarations
  int c;
  int y;
  int z;
  // pre-conditions
  (c = 0);
  assume((y >= 0));
  assume((y >= 127));
  (z = (36 * y));
  // loop body
  while (unknown()) {
    if ( (c < 36) )
    {
    (z  = (z + 1));
    (c  = (c + 1));
    }

  }
  // post-condition
if ( (z < 0) )
if ( (z >= 4608) )
assert( (c >= 36) );

}

int unknown() {

}
"""


# def strip_matching_brackets(s):
#     c = s.strip()
#     if c.startswith("(") and c.endswith(")"):
#         return strip_matching_brackets(c[1:-1])
#     return s


# def __get_query_string(cur_depth, max_depth):
#     if max_depth == 0:
#         return """((expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))
#         (#eq? @function-name "assert"))"""

#     elif cur_depth == 0:
#         return """(expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))"""

#     elif cur_depth < max_depth:
#         return (
#             """(if_statement (
#                 ((parenthesized_expression) @premise)
#                 """
#             + __get_query_string(cur_depth - 1, max_depth)
#             + """
#                 ))"""
#         )
#     elif cur_depth == max_depth:
#         return (
#             """((if_statement (
#                         ((parenthesized_expression) @premise)
#                         """
#             + __get_query_string(cur_depth - 1, max_depth)
#             + """
#                             ) @outer-if-statement
#                     )
#                     (#eq? @function-name "assert")
#                     )"""
#         )


# def get_query_string(n):
#     return __get_query_string(n, n)


bp = Code2InvParser("c")
ast = bp.parse(c_program)
print(bp.get_modified_asserts(c_program))

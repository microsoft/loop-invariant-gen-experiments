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

        matching_nodes = []
        ast_query_depth = 3

        while ast_query_depth >= 0:
            qs = self.get_query_string(ast_query_depth)
            matching_nodes = self.language.query(qs).captures(ast.root_node)
            if len(matching_nodes) > 0:
                break
            ast_query_depth -= 1

        if matching_nodes is []:
            return code

        premise = " ∧ ".join(
            [x[0].text.decode("utf-8") for x in matching_nodes if x[1] == "premise"]
        )
        conclusion = " ∧ ".join(
            [x[0].text.decode("utf-8") for x in matching_nodes if x[1] == "conclusion"]
        )

        if premise == "":
            post_c = "//@ assert " + conclusion + ";"
        else:
            post_c = "//@ assert " + premise + " => " + conclusion + ";"

        parent_node_type = "outer-if-statement" if ast_query_depth > 0 else "conclusion"
        parent_nodes = [x[0] for x in matching_nodes if x[1] == parent_node_type]

        if len(parent_nodes) > 1:
            print("Multiple parent nodes found. Using the first one.")

        parent_node = parent_nodes[0]

        new_c_program = code
        new_c_program = (
            code[: parent_node.parent.start_byte]
            + post_c
            + code[parent_node.parent.end_byte :]
        )

        return new_c_program

    def __get_query_string(self, cur_depth, max_depth):
        if max_depth == 0:
            return """((expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))
            (#eq? @function-name "assert"))"""

        elif cur_depth == 0:
            return """[(expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion)))
                            (_ (expression_statement (call_expression ((identifier) @function-name) ((argument_list) @conclusion))))]"""

        elif cur_depth < max_depth:
            return (
                """[(if_statement (
                    ((parenthesized_expression) @premise)
                    """
                + self.__get_query_string(cur_depth - 1, max_depth)
                + """))
                (_ (if_statement (
                    ((parenthesized_expression) @premise)
                    """
                + self.__get_query_string(cur_depth - 1, max_depth)
                + """
                    )))]"""
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

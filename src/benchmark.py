import os
import re
import string
from abc import ABC, abstractmethod
from datetime import datetime

from tree_sitter import Language, Parser


class Benchmark(ABC):
    @abstractmethod
    def __init__(self, benchmarks_file="", features=None, no_preprocess=True):
        self.input_benchmarks = os.path.join(
            os.path.dirname(__file__), "../", benchmarks_file
        )
        self.features = features
        lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
        self.language = Language(lib_path + "c-tree-sitter.so", "c")
        self.parser = Parser()
        self.parser.set_language(self.language)
        self.input_file_paths = []
        self.no_preprocess = no_preprocess

    @abstractmethod
    def preprocess(self, code, features=None):
        raise NotImplementedError

    @abstractmethod
    def combine_llm_outputs(self, checker_input, llm_outputs, features=None):
        """
        WARNING: Combines invariants from all completions.
        Takes an un-annotated checker input (processed-benchmarks)
        and annotated llm outputs, takes the annotation from llm outputs
        and adds it to the checker input them.
        """
        if not any("insert invariant" in line for line in checker_input.splitlines()):
            print(f"Ignoring since no insert invariant keyword")
            return ""

        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                if "invariant" in line and "insert invariants" not in line:
                    invariants.append(line.strip())

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "insert invariant" in line:
                loc = index
                break
        if loc is not None:
            lines = lines[: loc + 1] + invariants + lines[loc + 1 :]
        else:
            raise Exception("No 'insert invariant' found")
        output = "\n".join(lines)

        return output

    @abstractmethod
    def extract_loop_invariants(self, code):
        raise NotImplementedError

    @abstractmethod
    def get_variant_expressions(self, completions):
        raise NotImplementedError

    def validate_inputs(self, no_preprocess=False):
        if not os.path.exists(self.input_benchmarks):
            raise InvalidBenchmarkException(
                f"Input file {self.input_benchmarks} not found"
            )

        with open(self.input_benchmarks) as f:
            files = f.read().splitlines()
            for file in files:
                if not os.path.exists(file):
                    raise InvalidBenchmarkException(f"Benchmark file {file} not found")
                try:
                    code = None
                    with open(file) as f:
                        code = f.read()
                    if not no_preprocess:
                        self.preprocess(code, self.features)
                    self.input_file_paths.append(file)
                except InvalidBenchmarkException as e:
                    print(f"Error: {e.message}. File: {file}.")

        with open(
            datetime.now().strftime("benchmark_input_%Y_%m_%d_%H_%M_%S") + ".txt",
            "w",
        ) as f:
            f.write("\n".join(self.input_file_paths))
        return

    def get_code(self, file_path):
        code = None
        with open(file_path) as f:
            code = f.read()
        if self.no_preprocess:
            return code
        try:
            code = self.preprocess(code, self.features)
        except InvalidBenchmarkException as e:
            print(f"Error: {e.message}. File: {file_path}.")
        return code

    def remove_comments(self, code):
        """
        Removes all comments from the code
        """
        comment_query = self.language.query(
            """
            (comment) @comment 
            """
        )
        ast = self.parser.parse(bytes(code, "utf-8"))
        comments = comment_query.captures(ast.root_node)
        comments = sorted(comments, key=lambda x: x[0].start_byte, reverse=True)
        for comment in comments:
            if comment[0].text.decode().startswith("//@"):
                continue
            if comment[0].text.decode().startswith("/*@"):
                continue
            code = code[: comment[0].start_byte] + code[comment[0].end_byte :]
        return code

    def get_main_definition(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        main_query = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main_query.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            raise Exception("No single main definition found")
        return main_definition[0]

    def get_child_by_type(self, node, type):
        if node is None:
            return None
        for child in node.children:
            if child.type == type:
                return child
        return None

    def get_function_declarations(self, root):
        nodes = [root]
        function_declarations = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "declaration" and any(
                [c.type == "function_declarator" for c in node.children]
            ):
                declaration = self.get_child_by_type(node, "function_declarator")
                if declaration is None:
                    continue
                if self.get_child_by_type(declaration, "identifier") is None:
                    continue
                function_declarations.append(
                    (
                        node,
                        self.get_child_by_type(declaration, "identifier").text.decode(
                            "utf-8"
                        ),
                    )
                )
            else:
                nodes.extend(node.children)
        return function_declarations

    def remove_verifier_function_declarations(self, code):
        """
        Remove verifier function declarations
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        declarations = self.get_function_declarations(ast.root_node)
        declarations = [
            d
            for d, e in declarations
            if e.startswith("__VERIFIER_")
            or e == "__assert_fail"
            or e == "assume"
            or e == "abort"
            or e == "assert"
        ]
        declarations = sorted(declarations, key=lambda x: x.start_byte, reverse=True)
        for declaration in declarations:
            code = code[: declaration.start_byte] + code[declaration.end_byte :]
        return code

    def get_function_definitions(self, root):
        nodes = [root]
        function_definitions = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "function_definition":
                declaration = self.get_child_by_type(node, "function_declarator")
                if declaration is None:
                    continue
                identifier = self.get_child_by_type(declaration, "identifier")
                if identifier is None:
                    continue
                function_definitions.append((node, identifier.text.decode("utf-8")))
            else:
                nodes.extend(node.children)
        return function_definitions

    def remove_verifier_function_definitions(self, code):
        """
        Remove verifier function definitions
        """
        ast = self.parser.parse(bytes(code, "utf-8"))
        definitions = self.get_function_definitions(ast.root_node)
        definitions = [
            d
            for d, e in definitions
            if e.startswith("__VERIFIER_")
            or e == "reach_error"
            or e == "__assert_fail"
            or e == "__blast_assert"
            or e == "assume"
            or e == "abort"
            or e == "assert"
            or e == "assume_abort_if_not"
        ]
        definitions = sorted(definitions, key=lambda x: x.start_byte, reverse=True)
        for definition in definitions:
            code = code[: definition.start_byte] + code[definition.end_byte :]
        return code

    def clean_newlines(self, code):
        lines = code.splitlines()
        new_code = []
        for i, line in enumerate(lines):
            if (line.strip() == "") and (i > 0 and lines[i - 1].strip() == ""):
                continue
            else:
                new_code.append(line)
        return "\n".join(new_code)

    def get_function_calls(self, root):
        function_calls = []
        nodes = [root]
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "call_expression":
                identifier = self.get_child_by_type(node, "identifier")
                if identifier is None:
                    continue
                function_calls.append(
                    (
                        node,
                        identifier.text.decode("utf-8"),
                    )
                )
                nodes.extend(node.children)
            else:
                nodes.extend(node.children)
        return function_calls

    def replace_nondets_and_assert_assumes(self, code):
        """
        Replace all nondet functions with unknowns
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        # replace nondet calls with unknowns
        nondets = self.get_function_calls(root)
        verifier_nondet_calls = list(
            filter(
                lambda x: len(re.findall(r"^(__VERIFIER_)?nondet(.*)", x[1])) > 0,
                nondets,
            )
        )
        verifier_nondet_calls = sorted(
            verifier_nondet_calls, key=lambda x: x[0].start_byte, reverse=True
        )
        for nondet_call in verifier_nondet_calls:
            code = (
                code[: nondet_call[0].start_byte]
                + "unknown"
                + (
                    "_int()"
                    if not "_" in nondet_call[0].text.decode("utf-8")
                    else (
                        "_" + nondet_call[0].text.decode("utf-8").split("_")[-1].lower()
                    )
                )
                + code[nondet_call[0].end_byte :]
            )

        return self.replace_assumes(self.replace_asserts(code))

    def replace_assumes(self, code):
        """
        Replace __VERIFIER_assume calls with assumes
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        nondets_assert_assumes = self.get_function_calls(root)
        verifier_assume_calls = list(
            filter(
                lambda x: len(
                    re.findall(r"^(__VERIFIER_assume|assume_abort_if_not)", x[1])
                )
                > 0,
                nondets_assert_assumes,
            )
        )
        verifier_assume_calls = sorted(
            verifier_assume_calls, key=lambda x: x[0].start_byte, reverse=True
        )
        for assume_call in verifier_assume_calls:
            code = (
                code[: assume_call[0].start_byte]
                + re.sub(
                    r"^(__VERIFIER_assume|assume_abort_if_not)",
                    "assume",
                    assume_call[0].text.decode("utf-8"),
                )
                + code[assume_call[0].end_byte :]
            )

        return code

    def replace_asserts(self, code):
        """
        Replace __VERIFIER_assert/sassert/assert calls with asserts
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        assert_assumes = self.get_function_calls(root)
        assert_assumes = sorted(
            assert_assumes, key=lambda x: x[0].start_byte, reverse=True
        )
        assert_assumes = [a[0].parent for a in assert_assumes]
        verifier_assert_calls = list(
            filter(
                lambda x: len(
                    re.findall(
                        r"^((__VERIFIER_|s)?assert)\s*(\(.*\))\s*;.*",
                        x.text.decode("utf-8"),
                    )
                )
                > 0,
                assert_assumes,
            )
        )
        verifier_assert_calls = sorted(
            verifier_assert_calls, key=lambda x: x.start_byte, reverse=True
        )

        for assert_call in verifier_assert_calls:
            code = (
                code[: assert_call.start_byte]
                + re.sub(
                    r"^(__VERIFIER_|s)?assert\s*(?P<arg>\(.*\))\s*;(?P<rest>.*)",
                    r"{;\n//@ assert\g<arg>;" + "\n" + r"}\n\g<rest>",
                    assert_call.text.decode("utf-8"),
                )
                + code[assert_call.end_byte :]
            )

        return code

    def analyze_main(self, code):
        """
        Some benchmarks have a missing return type for main.
        Default this type to int, and make sure the return type
        matches the value being returned.
        """
        code = re.sub(r"^\s*main\s*\(", "int main(", code, flags=re.MULTILINE)

        main_definition = self.get_main_definition(code)
        main_definition_type = main_definition.child_by_field_name("type")
        if main_definition_type is None:
            return "ERROR: No return type for main function"
        main_definition_type = main_definition_type.text.decode("utf-8")

        return_stmt = self.language.query(
            """
            (return_statement) @return_stmt
            """
        )
        return_stmt = return_stmt.captures(main_definition)
        return_stmt = sorted(return_stmt, key=lambda x: x[0].start_byte, reverse=True)
        if len(return_stmt) < 1:
            return code

        if main_definition_type == "void":
            for rv in return_stmt:
                code = code[: rv[0].start_byte] + "\nreturn;\n" + code[rv[0].end_byte :]
        else:
            for rv in return_stmt:
                return_value = [
                    x for x in rv[0].children if x.type != "return" and x.type != ";"
                ]
                code = (
                    code[: rv[0].start_byte]
                    + (
                        rv[0].text.decode("utf-8")
                        if len(return_value) > 0
                        else "\nreturn 0;\n"
                    )
                    + code[rv[0].end_byte :]
                )

        return code

    def remove_preprocess_lines(self, code):
        """
        Removes all preprocessor lines from the code
        """
        lines = code.split("\n")
        lines = list(filter(lambda x: not re.match(r"^#\s\d+\s.*", x), lines))
        return "\n".join(lines)

    def remove_local_includes(self, code):
        """
        Removes all local includes from the code
        """
        lines = code.split("\n")
        lines = list(filter(lambda x: not re.match(r"^#include \".*\"", x), lines))
        return "\n".join(lines)

    def has_ill_formed_asserts(self, code):
        """Should be called in the end of preprocessing.
        This checks if there are any __VERIFIER_assert calls left in the code.
        If there are, the code is ill-formed, because the verifier functions
        should have been removed in the preprocessing.
        """
        ast = self.parser.parse(bytes(code, "utf-8"))
        root = ast.root_node
        function_calls = self.get_function_calls(root)
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)
            function_calls = self.get_function_calls(root)

        function_calls = [
            f
            for f in function_calls
            if f[1] == "__VERIFIER_assert" or f[1] == "reach_error"
        ]

        if len(function_calls) > 0:
            return True

    def is_interprocedural(self, code):
        """should be called after all __VERIFIER_ functions are removed.
        and after main is fixed."""

        # get main function
        main_definition = self.get_main_definition(code)

        calls = self.get_function_calls(main_definition)
        calls = [
            c for c in calls if not re.match(r"(abort|exit|assume|unknown.*)", c[1])
        ]

        return len(calls) > 0

    def add_boiler_plate(self, code):
        """
        Add hash defines and externs for unknown functions
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        main_definition = self.get_main_definition(code)
        main_definition_type = main_definition.child_by_field_name("type")

        code = (
            ("#include <stdlib.h>\n#define assume(e) if(!(e)) exit(-1);\n")
            + (
                "#define abort() exit(-2);\n"
                if len(re.findall(r"abort\s*\(\s*\)", code)) > 0
                else ""
            )
            + ("#define LARGE_INT 1000000\n" if "LARGE_INT" in code else "")
            + ("extern int unknown(void);\n" if "unknown()" in code else "")
            + ("extern int unknown_int(void);\n" if "unknown_int()" in code else "")
            + (
                "extern unsigned int unknown_uint(void);\n"
                if "unknown_uint" in code
                else ""
            )
            + ("extern _Bool unknown_bool(void);\n" if "unknown_bool()" in code else "")
            + ("extern char unknown_char(void);\n" if "unknown_char()" in code else "")
            + (
                "extern unsigned short unknown_ushort(void);\n"
                if "unknown_ushort()" in code
                else ""
            )
            + (
                "extern unsigned char unknown_uchar(void);\n"
                if "unknown_uchar()" in code
                else ""
            )
            + "\n"
            + code
        )
        return code

    def get_error_labels(self, root):
        nodes = [root]
        error_nodes = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "labeled_statement":
                if node.child_by_field_name("label").text.decode("utf-8") == "ERROR":
                    error_nodes.append(node)
            nodes += node.children
        return error_nodes

    def get_loops(self, root):
        nodes = [root]
        loops = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "while_statement" or node.type == "for_statement":
                loops.append(node)
            elif node.type == "do_statement" and any(
                [c.type == "while" for c in node.children]
            ):
                loops.append(node)
            nodes += node.children
        return loops

    def get_total_loop_count(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        nodes = [ast.root_node]
        loops = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "while_statement" or node.type == "for_statement":
                loops.append(node)
            elif node.type == "do_statement" and any(
                [c.type == "while" for c in node.children]
            ):
                loops.append(node)
            nodes += node.children
        return len(loops)

    def uses_arrays(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        nodes = [ast.root_node]
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "array_declarator":
                return True
            nodes += node.children
        return False

    def uses_pointers(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        nodes = [ast.root_node]
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "pointer_declarator":
                return True
            nodes += node.children
        return False

    def uses_floats_or_doubles(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        nodes = [ast.root_node]
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "primitive_type":
                if (
                    node.text.decode("utf-8") == "float"
                    or node.text.decode("utf-8") == "double"
                ):
                    return True
            nodes += node.children
        return False

    def add_loop_labels(self, code):
        labels = string.ascii_uppercase
        ast = self.parser.parse(bytes(code, "utf-8"))

        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        loops = self.get_loops(root)
        loops = sorted(loops, key=lambda x: x.start_byte, reverse=True)

        for i, l in enumerate(loops):
            loop_label = "/* Loop_" + labels[len(loops) - i - 1] + " */  "
            code = code[: l.start_byte] + loop_label + code[l.start_byte :]
        return code

    def is_multi_loop(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)
        loops = self.get_loops(root)
        return len(loops) > 1

    def remove_reach_error_calls(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        function_calls = self.get_function_calls(root)
        function_calls = sorted(
            function_calls, key=lambda x: x[0].start_byte, reverse=True
        )
        for function_call in function_calls:
            if (
                function_call[1] == "reach_error"
                or function_call[1] == "__blast_assert"
            ):
                code = (
                    code[: function_call[0].start_byte]
                    + "{; \n//@ assert(\\false);\n}"
                    + code[function_call[0].end_byte :]
                )

        return code

    def add_method_labels(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        function_definitions = self.get_function_definitions(ast.root_node)
        function_definitions = sorted(
            function_definitions, key=lambda x: x[0].start_byte, reverse=True
        )
        for function_definition in function_definitions:
            code = (
                code[: function_definition[0].start_byte]
                + "\n/* Function_"
                + function_definition[1]
                + " */\n"
                + code[function_definition[0].start_byte :]
            )
        return code

    def any_child_satisfies(self, node, lambda_fn):
        if lambda_fn(node):
            return True
        for child in node.children:
            if self.any_child_satisfies(child, lambda_fn):
                return True
        return False

    def all_functions_defined_in_program(self, input_code):
        ast = self.parser.parse(bytes(input_code, "utf8"))
        root_node = ast.root_node
        functions = self.get_function_definitions(root_node)
        function_names = [f[1] for f in functions]

        function_calls = self.get_function_calls(root_node)
        function_calls = [f[0].text.decode("utf-8") for f in function_calls]

        for f in function_calls:
            f_call = f.split("(")[0].strip()
            if f_call == "assume" or f_call == "abort" or f_call == "exit":
                continue
            fname = re.match(
                r"unknown_(int|uint|bool|float|double|char|uchar|long|ulong)", f_call
            )
            if fname is not None:
                continue
            if f_call not in function_names:
                return False

        return True


class InvalidBenchmarkException(Exception):
    def __init__(self, message):
        self.message = message
        super().__init__(self.message)

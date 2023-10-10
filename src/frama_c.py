import csv
import datetime
import json
import os
import random
import re
import string
import subprocess
import sys
from copy import deepcopy

from benchmark import Benchmark, InvalidBenchmarkException
from checker import Checker
from tree_sitter import Language, Parser


class FramaCChecker(Checker):
    def __init__(self):
        super().__init__("frama-c")

    def is_invariant(self, line):
        inv = re.findall(r"loop invariant (.+);", line)
        return len(inv) > 0

    def is_variant(self, line):
        inv = re.findall(r"loop variant (.+);", line)
        return len(inv) > 0

    def get_annotation_error_from_kernel_logs(self, error_line):
        line_num = re.search(r"\:(\d+)\:", error_line)
        if line_num is not None:
            line_num = int(line_num.group(1))
        error_message = re.search(r"\[kernel\:annot-error\] warning: (.+)", error_line)
        if error_message is not None:
            error_message = error_message.group(1)
        error_message = f"Annotation error on line {line_num}: {error_message}"
        return error_message

    def check(self, input, check_variant, verbose=False, use_json_output=False):
        temp_file = datetime.datetime.now().strftime(
            "/tmp/temp_eval_%Y_%m_%d_%H_%M_%S_"
        ) + str(random.randint(0, 1000000))
        temp_c_file = temp_file + "_.c"
        temp_wp_json_report_file = temp_file + "_wp_report.json"
        temp_kernel_log_file = temp_file + "_kernel_logs.txt"
        temp_output_dump_file = temp_file + "_output_dump.csv"

        with open(temp_c_file, "w") as f:
            f.write(input)

        if verbose:
            print("==============================")
        cmd = f"frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 \
                -wp-prover=alt-ergo,z3,cvc4 {temp_c_file} -wp-report-json {temp_wp_json_report_file} -kernel-warn-key annot-error=active \
                -kernel-log a:{temp_kernel_log_file} -then -no-unicode -report -report-csv {temp_output_dump_file}"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        frama_c_std_output, err = p.communicate()

        # Look for errors in the kernel logs
        if not os.path.exists(temp_kernel_log_file):
            return False, "No kernel logs found"
        with open(temp_kernel_log_file, "r", encoding="utf-8") as f:
            kernel_logs = f.read()
            kl_lines = kernel_logs.splitlines()
            # if len(kl_lines) > 1:
            # print("More than 1 line in Frama-C kernel logs.")
            # print(kernel_logs)
            error_line = None
            for line in kl_lines:
                if "[kernel:annot-error]" in line:
                    error_line = line
                    break
                else:
                    continue
            if error_line is not None:
                error_message = self.get_annotation_error_from_kernel_logs(error_line)
                if "unexpected token ''" in error_message:
                    error_message = "No invariants found."
                return False, error_message

        checker_output = []
        success = False

        if use_json_output:
            if not os.path.exists(temp_wp_json_report_file):
                return False, "No JSON report found"

            with open(temp_wp_json_report_file, "r", encoding="utf-8") as f:
                json_output = f.read()
                json_output = re.sub(r"(\d+)\.,", r"\1.0,", json_output)
                json_output = json.loads(json_output)
                loop_invariant_status = {}
                for item in json_output:
                    if "_loop_invariant_" in item["goal"]:
                        inv_id = re.findall(
                            r"_loop_invariant_(i\d+)_(preserved|established)",
                            item["goal"],
                        )
                        if len(inv_id) == 0:
                            # item is an assertion
                            continue
                        inv_id = inv_id[0]
                        if inv_id[0] not in loop_invariant_status:
                            loop_invariant_status[inv_id[0]] = {}
                        loop_invariant_status[inv_id[0]][inv_id[1]] = item["passed"]

                assert all(
                    [
                        (
                            len(loop_invariant_status[inv_id]) == 2
                            and "preserved" in loop_invariant_status[inv_id].keys()
                            and "established" in loop_invariant_status[inv_id].keys()
                        )
                        for inv_id in loop_invariant_status
                    ]
                )
                success = all(
                    [
                        loop_invariant_status[inv_id]["preserved"]
                        and loop_invariant_status[inv_id]["established"]
                        for inv_id in loop_invariant_status
                    ]
                )

                invariants_with_ids = self.get_invariants_with_ids(input.splitlines())

                for inv in sorted(
                    loop_invariant_status.keys(), key=lambda x: int(x[1:])
                ):
                    if (
                        loop_invariant_status[inv]["preserved"]
                        and loop_invariant_status[inv]["established"]
                    ):
                        checker_output.append(
                            f"loop invariant {invariants_with_ids[inv]} is inductive."
                        )
                    elif (
                        not loop_invariant_status[inv]["preserved"]
                        and loop_invariant_status[inv]["established"]
                    ):
                        checker_output.append(
                            f"loop invariant {invariants_with_ids[inv]} is established but not preserved."
                        )
                    elif (
                        loop_invariant_status[inv]["preserved"]
                        and not loop_invariant_status[inv]["established"]
                    ):
                        checker_output.append(
                            f"loop invariant {invariants_with_ids[inv]} is preserved but not established."
                        )
                    else:
                        checker_output.append(
                            f"loop invariant {invariants_with_ids[inv]} is neither established nor preserved."
                        )

                checker_output = "\n".join(checker_output)

        else:
            # Parse the output dump
            if not check_variant and not os.path.exists(temp_output_dump_file):
                return False, "No CSV output dump found from Frama-C"

            with open(temp_output_dump_file, "r", encoding="utf-8") as f:
                checker_output = [row for row in csv.DictReader(f, delimiter="\t")]

                success = all(
                    row["status"] == "Valid"
                    for row in checker_output
                    if row["property kind"] == "loop invariant"
                    or row["property kind"] == "user assertion"
                )

                checker_output = "\n".join(
                    [
                        f"Invariant {row['property']} on line {row['line']}: {row['status']}"
                        for row in checker_output
                        if row["property kind"] == "loop invariant"
                    ]
                )

        if not check_variant and not os.path.exists(temp_output_dump_file):
            return False, "No CSV output dump found from Frama-C"

        with open(temp_output_dump_file, "r", encoding="utf-8") as f:
            assertion_output = [row for row in csv.DictReader(f, delimiter="\t")]

            success = success and all(
                row["status"] == "Valid"
                for row in assertion_output
                if row["property kind"] == "user assertion"
            )

            user_assertion = "\n".join(
                [
                    f"Assertion {row['property']}: "
                    + (
                        f"Unproven"
                        if row["status"] == "Unknown"
                        else f"{row['status']}"
                    )
                    for row in assertion_output
                    if row["property kind"] == "user assertion"
                ]
            )

        checker_output = checker_output + "\n" + user_assertion + "\n"

        if check_variant:
            # print(str(frama_c_std_output, "UTF-8"))
            msg = str(frama_c_std_output, "UTF-8").split("\n")
            result = list(filter(lambda x: "Loop variant" in x, msg))
            if len(result) < 1:
                print("No variant found (wrong mode?)")
                return False, "No variant found (wrong mode?)"

            if "Valid" in result[0]:
                checker_output = checker_output + "Loop variant is Valid.\n"
                success = success and True
            else:
                checker_output = checker_output + "Loop variant is Invalid.\n"
                success = False

        os.remove(temp_c_file)
        os.remove(temp_wp_json_report_file)
        os.remove(temp_kernel_log_file)
        os.remove(temp_output_dump_file)

        return success, checker_output

    def get_line_no_from_error_msg(self, checker_output):
        pattern = r"Annotation error on line (\d+): "
        matches = re.findall(pattern, checker_output)
        line_numbers = [int(match) - 1 for match in matches]

        return line_numbers

    def get_unknown_inv_no_from_error_msg(self, checker_output):
        checker_out = "".join(
            [c for c in checker_output.splitlines() if c.startswith("Invariant ")]
        )
        pattern = r"on line (\d+): Unknown"
        matches = re.findall(pattern, checker_out)
        line_numbers = [int(match) - 1 for match in matches]

        return line_numbers

    def get_partially_proven_inv_from_error_msg(self, checker_output):
        checker_output = "".join(
            [c for c in checker_output.splitlines() if c.startswith("Invariant ")]
        )
        pattern = r"on line (\d+): Partially proven"
        matches = re.findall(pattern, checker_output)
        line_numbers = [int(match) - 1 for match in matches]

        return line_numbers

    def get_incorrect_invariants(self, code, error):
        line_numbers = self.get_line_no_from_error_msg(error)
        lines = code.splitlines()
        incorrect_invariants = []
        for line_number in line_numbers:
            if self.is_invariant(lines[int(line_number)]):
                incorrect_invariants.append(lines[int(line_number)].strip())
        return "\n".join(incorrect_invariants)

    def get_invariants(self, lines):
        invariants = []
        invariant_expressions = []
        for line in lines:
            if self.is_invariant(line):
                inv = re.findall(r"(loop invariant (i\d+: )?(.+);)", line)[0]
                if inv[2] not in invariant_expressions:
                    invariants.append(inv[0])
                    invariant_expressions.append(inv[2])
        return invariants

    def get_invariants_with_ids(self, lines):
        invariants = {}
        for line in lines:
            if self.is_invariant(line):
                inv = re.findall(r"loop invariant (\w+:)?(.+);", line)[0]
                invariants[inv[0].rstrip(":")] = inv[1].strip()
        return invariants

    def get_invariants_count(self, code):
        return len(self.get_invariants(code.splitlines()))

    def get_variants(self, lines):
        variants = []
        for line in lines:
            if self.is_variant(line):
                inv = re.findall(r"(loop variant .+;)", line)[0]
                if inv not in variants:
                    variants.append(inv)
        return variants

    def get_non_inductive_invariant_line_nos(self, checker_message, checker_input):
        lines = checker_message.splitlines()
        non_inductive_invariants = []
        for line in lines:
            if "is inductive." in line:
                continue
            else:
                inv_exp = re.findall(r"loop invariant (.+) is", line)
                if len(inv_exp) == 1:
                    non_inductive_invariants.append(inv_exp[0])

        non_inductive_invariant_line_nos = []
        for i, line in enumerate(checker_input.splitlines()):
            if self.is_invariant(line):
                for inv in non_inductive_invariants:
                    if "loop invariant " in line and inv in line:
                        non_inductive_invariant_line_nos.append(i)
                        break

        return non_inductive_invariant_line_nos

    def prune_annotations_and_check(
        self, input_code, features, verbose=False, use_json_output=False
    ):
        print("Pruning annotations...")

        annotation_line_mapping = {}
        lines = input_code.splitlines()
        for no, line in enumerate(lines):
            if self.is_invariant(line) or self.is_variant(line):
                annotation_line_mapping[no] = line

        if len(annotation_line_mapping) == 0:
            raise Exception("No invariants/variants found")

        inv_line_list = list(annotation_line_mapping.keys())

        (invariant_line_start, invariant_line_end) = (
            inv_line_list[0],
            inv_line_list[-1],
        )

        input_code = "\n".join(
            lines[:invariant_line_start]
            + self.get_invariants(lines)
            + self.get_variants(lines)
            + lines[invariant_line_end + 1 :]
        )
        code_queue = [input_code]
        num_frama_c_calls = 0

        while len(code_queue) > 0 and num_frama_c_calls < 1000:
            input_code = code_queue.pop(0)
            code_lines = input_code.splitlines()
            if (
                len(self.get_invariants(lines)) == 0
                and len(self.get_variants(lines)) == 0
            ):
                print("No invariants/variants found")
                continue
            status, checker_message = self.check(
                input_code,
                ("termination" in features),
                verbose,
                use_json_output=use_json_output,
            )

            if verbose:
                print(checker_message)

            if status:
                if verbose:
                    print("Proved")
                break

            if "Annotation error " in checker_message:
                # TODO: Why not remove all annotation errors?
                # A: Frama-C panics and skips the entire annotation block
                # as soon as it sees an annotation error.
                # So we get only one annotation error at a time.
                annotation_error_line_no = self.get_line_no_from_error_msg(
                    checker_message
                )[0]

                if verbose:
                    print(
                        "Removing (syntax error): ",
                        code_lines[annotation_error_line_no],
                    )
                print("Removing line " + code_lines[annotation_error_line_no])
                code_lines[annotation_error_line_no] = ""
                input_code = "\n".join(code_lines)
                code_queue.append(input_code)

            elif use_json_output:
                non_inductive_invariant_line_nos = (
                    self.get_non_inductive_invariant_line_nos(
                        checker_message, input_code
                    )
                )
                if len(non_inductive_invariant_line_nos) > 0:
                    for line_no in non_inductive_invariant_line_nos:
                        if verbose:
                            print("Removing (non-inductive): ", code_lines[line_no])
                        code_lines[line_no] = ""
                    code_queue.append("\n".join(code_lines))

            else:
                # TODO: What about TIMEOUT?
                # If any invariant causes a Timeout, it's marked as "Unknown"
                # because the prover could not prove it. So removing it for now.
                unknown_inv_lines = self.get_unknown_inv_no_from_error_msg(
                    checker_message
                )
                if len(unknown_inv_lines) > 0:
                    for line_no in unknown_inv_lines:
                        if verbose:
                            print("Removing (proof fail): ", code_lines[line_no])
                        code_lines[line_no] = ""
                    code_queue.append("\n".join(code_lines))
                else:
                    # Push code with one "Partially proven" invariant removed to the queue
                    partially_proven_inv_line_nos = (
                        self.get_partially_proven_inv_from_error_msg(checker_message)
                    )
                    if self.get_invariants_count(input_code) == len(
                        partially_proven_inv_line_nos
                    ):
                        # If all invariants are partially proven, then we can't afford
                        # to prune further. example, there's an assertion inside the loop which is Unknown
                        break
                    if verbose:
                        if len(partially_proven_inv_line_nos) > 0:
                            print("Forking: All partially proven invariants.")
                        else:
                            print("No partially proven invariant")

                    for line_no in partially_proven_inv_line_nos:
                        code_lines__ = deepcopy(code_lines)
                        code_lines__[line_no] = ""
                        code_queue.append("\n".join(code_lines__))
            num_frama_c_calls += 1

        if num_frama_c_calls == 1000:
            print("Crossed 1000 iterations. Stopping pruning...")

        if not status:
            print(
                "Invariants/variant not strong enough to prove or benchmark is invalid."
            )
        else:
            print("Found strong enough invariants/variant.")

        return status, input_code, num_frama_c_calls


class FramaCBenchmark(Benchmark):
    def __init__(self, llm_input_file="", features=None):
        super().__init__(llm_input_file, features)
        lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
        self.language = Language(lib_path + "c-tree-sitter.so", "c")
        self.parser = Parser()
        self.parser.set_language(self.language)
        self.features = features

    def combine_llm_outputs(self, checker_input, llm_outputs, features):
        invariants = {}
        variant = None
        if "multiple_methods" in features:
            raise Exception("multiple_methods not supported yet")

        elif "multiple_loops_one_method" == features:
            print("Combining invariants from {} outputs".format(len(llm_outputs)))

            invariants = {}
            for llm_output in llm_outputs:
                lines = llm_output.splitlines()
                for line in lines:
                    label = re.findall(r"Loop([A-Z]):", line)
                    if len(label) > 0:
                        label = label[0]
                        if label not in invariants:
                            invariants[label] = []

                        invariant = re.findall(r"(loop invariant .+;)", line)
                        if len(invariant) > 0:
                            invariants[label].append(invariant[0])
            output = ""
            multi_loop = re.findall(r"/\* Loop([A-Z]) \*/", checker_input)
            if len(multi_loop) > 0:
                for loop_label in multi_loop:
                    new_checker_input = re.sub(
                        r"/\* Loop" + loop_label + r" \*/",
                        "/*@\n" + "\n".join(invariants[loop_label]) + "\n*/\n",
                        new_checker_input,
                    )
                output = new_checker_input

            return output

        elif "termination_one_loop_one_method" == features:
            annotated_candidates = []
            invariants = {}
            inv_count = 0
            variants = {}

            for llm_output in llm_outputs:
                for line in llm_output.split("\n"):
                    invariant = re.findall(r"loop invariant (.+);", line)
                    __variants = re.findall(r"(loop variant .+;)", line)
                    if len(invariant) > 0:
                        inv_id = re.findall(r"loop invariant (\w+:) ", line)
                        if len(inv_id) > 0:
                            invariant = [invariant[0].replace(inv_id[0], "")]
                        invariant = f"loop invariant i{inv_count + 1}: {invariant[0]};"  # add loop invariant label
                        invariants[invariant] = True
                        inv_count += 1

                    for variant in __variants:
                        variants[variant] = True

            loop = self.get_loops(self.get_main_definition(checker_input))
            if len(loop) != 1:
                raise Exception(
                    "No singular loop found while adding annotations. Multiple loops not supported yet."
                )
            loop = loop[0]

            for variant in variants.keys():
                annotated_candidates.append(
                    checker_input[: loop.start_byte]
                    + "/*@\n"
                    + "\n".join(list(invariants.keys()))
                    + "\n"
                    + variant
                    + "\n*/\n"
                    + checker_input[loop.start_byte :]
                )

            return annotated_candidates

        elif "one_loop_one_method" in features:
            invariants = {}
            inv_count = 0
            for llm_output in llm_outputs:
                lines = llm_output.splitlines()
                for line in lines:
                    invariant = re.findall(r"loop invariant (.+);", line)
                    if len(invariant) > 0:
                        inv_id = re.findall(r"loop invariant (\w+:) ", line)
                        if len(inv_id) > 0:
                            invariant = [invariant[0].replace(inv_id[0], "")]
                        invariant = f"loop invariant i{inv_count + 1}: {invariant[0]};"  # add loop invariant label
                        invariants[invariant] = True
                        inv_count += 1

            loop = self.get_loops(self.get_main_definition(checker_input))
            if len(loop) != 1:
                raise Exception("No singular loop found while adding annotations")
            loop = loop[0]
            output = (
                checker_input[: loop.start_byte]
                + "/*@\n"
                + "\n".join(list(invariants.keys()))
                + "\n*/\n"
                + checker_input[loop.start_byte :]
            )

            return output

        else:
            raise Exception("Unknown feature set")

    def remove_comments(self, code):
        comment_query = self.language.query(
            """
            (comment) @comment 
            """
        )
        ast = self.parser.parse(bytes(code, "utf-8"))
        comments = comment_query.captures(ast.root_node)
        comments = sorted(comments, key=lambda x: x[0].start_byte, reverse=True)
        for comment in comments:
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
            return "ERROR: No main function found"
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
        ast = self.parser.parse(bytes(code, "utf-8"))

        declarations = self.get_function_declarations(ast.root_node)
        declarations = [d for d, e in declarations if e.startswith("__VERIFIER_")]
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
        ast = self.parser.parse(bytes(code, "utf-8"))
        definitions = self.get_function_definitions(ast.root_node)
        definitions = [
            d
            for d, e in definitions
            if e.startswith("__VERIFIER_") or e == "reach_error"
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

    def get_function_calls(self, main):
        function_calls = []
        nodes = [main]
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "call_expression":
                print(node.text.decode("utf-8"))
                function_calls.append(
                    (
                        node,
                        self.get_child_by_type(node, "identifier").text.decode("utf-8"),
                    )
                )
            else:
                nodes.extend(node.children)
        return function_calls

    def replace_nondets_and_assert_assumes(self, code):
        # get main
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
            return "ERROR: No main function found"
        main_definition = main_definition[0]

        # replace nondet calls with unknowns
        nondets_assert_assumes = self.get_function_calls(main_definition)
        verifier_nondet_calls = list(
            filter(
                lambda x: len(
                    re.findall(r"^(__VERIFIER_)?nondet(.*)", x[0].text.decode("utf-8"))
                )
                > 0,
                nondets_assert_assumes,
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
        # replace __VERIFIER_assume calls with assumes
        main_query = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = main_query.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]
        if len(main_definition) != 1:
            raise InvalidBenchmarkException("No main function found")

        main_definition = main_definition[0]
        nondets_assert_assumes = self.get_function_calls(main_definition)
        verifier_assume_calls = list(
            filter(
                lambda x: len(
                    re.findall(r"^__VERIFIER_assume", x[0].text.decode("utf-8"))
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
                    r"^(__VERIFIER_assume)",
                    "assume",
                    assume_call[0].text.decode("utf-8"),
                )
                + code[assume_call[0].end_byte :]
            )

        return code

    def replace_asserts(self, code):
        # replace __VERIFIER_assert/sassert calls with asserts
        main_query = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = main_query.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]
        if len(main_definition) != 1:
            raise InvalidBenchmarkException("No main function found")
        main_definition = main_definition[0]

        assert_assumes = self.get_function_calls(main_definition)
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
                    r"^(__VERIFIER_|s)?assert\s*(?P<arg>\(.*\));(?P<rest>.*)",
                    r"{;\n//@ assert\g<arg>;" + "\n" + r"\g<rest>}",
                    assert_call.text.decode("utf-8"),
                )
                + code[assert_call.end_byte :]
            )

        return code

    def analyze_main(self, code):
        # Fix missing type for main. Default to int.
        code = re.sub(r"^\s*main\s*\(", "int main(", code, flags=re.MULTILINE)

        ast = self.parser.parse(bytes(code, "utf-8"))
        main = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            return "ERROR: No main function found"

        main_definition = main_definition[0]
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
                code = code[: rv[0].start_byte] + "return;" + code[rv[0].end_byte :]
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
                        else "return 0;"
                    )
                    + code[rv[0].end_byte :]
                )

        return code

    def remove_preprocess_lines(self, code):
        lines = code.split("\n")
        lines = list(filter(lambda x: not re.match(r"^#\s\d+\s.*", x), lines))
        return "\n".join(lines)

    def remove_local_includes(self, code):
        lines = code.split("\n")
        lines = list(filter(lambda x: not re.match(r"^#include \".*\"", x), lines))
        return "\n".join(lines)

    def remove_tmpl(self, code):
        lines = code.split("\n")
        lines = list(map(lambda x: re.sub(r"tmpl\s*\(.*\)\s*;", "", x), lines))
        return "\n".join(lines)

    def has_ill_formed_asserts(self, code):
        """Should be called in the end of preprocessing.
        This checks if there are any __VERIFIER_assert calls left in the code.
        If there are, the code is ill-formed, because the verifier functions
        should have been removed in the preprocessing.
        """
        if len(re.findall(r"__VERIFIER_assert", code)) > 0:
            return True

    def is_interprocedural(self, code):
        """should be called after all __VERIFIER_ functions are removed.
        and after main is fixed."""

        # get main function
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            return "ERROR: No main function found"

        main_definition = main_definition[0]

        # catch non assume assert function calls
        function_calls = self.language.query(
            """
            (call_expression) @function_call
            """
        )
        function_calls = function_calls.captures(main_definition)
        function_calls = [
            f
            for f in function_calls
            if f[1] == "function_call"
            and not re.match(r"(assert|assume|unknown.*)", f[0].text.decode("utf-8"))
        ]

        return len(function_calls) != 0

    def add_boiler_plate(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            return "ERROR: No main function found"

        main_definition = main_definition[0]
        main_definition_type = main_definition.child_by_field_name("type")

        code = (
            (
                "#define assume(e) if(!(e)) return;\n"
                if main_definition_type.text.decode("utf-8") == "void"
                else "#define assume(e) if(!(e)) return 0;\n"
            )
            + ("#define LARGE_INT 1000000\n" if "LARGE_INT" in code else "")
            + ("extern int unknown(void);\n" if "unknown" in code else "")
            + ("extern int unknown_int(void);\n" if "unknown_int" in code else "")
            + (
                "extern unsigned int unknown_uint(void);\n"
                if "unknown_uint" in code
                else ""
            )
            + ("extern _Bool unknown_bool(void);\n" if "unknown_bool" in code else "")
            + ("extern char unknown_char(void);\n" if "unknown_char" in code else "")
            + (
                "extern unsigned short unknown_ushort(void);\n"
                if "unknown_ushort" in code
                else ""
            )
            + "\n"
            + code
        )
        return code

    def get_error_labels(self, main_node):
        nodes = [main_node]
        error_nodes = []
        while len(nodes) > 0:
            node = nodes.pop()
            if node.type == "labeled_statement":
                if node.child_by_field_name("label").text.decode("utf-8") == "ERROR":
                    error_nodes.append(node.child_by_field_name("label"))
            nodes += node.children
        return error_nodes

    def add_frama_c_asserts(self, code):
        # get main function
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            return "ERROR: No main function found"

        main_definition = main_definition[0]

        # catch ERROR: in main
        errors = self.get_error_labels(main_definition)
        errors = sorted(errors, key=lambda x: x.start_byte, reverse=True)
        for e in errors:
            code = (
                code[: e.end_byte + 1]  # +1 to account for the colon
                + "{; \n//@ assert(\\false);\n}"
                + code[e.end_byte + 1 :]
            )

        return code

    def get_loops(self, main_definition):
        nodes = [main_definition]
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

    def add_loop_labels(self, code):
        labels = string.ascii_uppercase
        ast = self.parser.parse(bytes(code, "utf-8"))
        main = self.language.query(
            """
            (((function_definition (function_declarator (identifier) @function_name)) @main_definition)
            (#eq? @function_name "main"))
            """
        )
        main = main.captures(ast.root_node)
        main_definition = [m[0] for m in main if m[1] == "main_definition"]

        if len(main_definition) != 1:
            return "ERROR: No main function found"

        main_definition = main_definition[0]

        loops = self.get_loops(main_definition)
        loops = sorted(loops, key=lambda x: x.start_byte, reverse=True)

        for i, l in enumerate(loops):
            loop_label = "/* Loop" + labels[len(loops) - i - 1] + " */  "
            code = code[: l.start_byte] + loop_label + code[l.start_byte :]
        return code

    def is_multi_loop(self, code):
        main_definition = self.get_main_definition(code)
        loops = self.get_loops(main_definition)
        return len(loops) > 1

    def apply_patches(self, code):
        # All last minute patches go here
        while_true_loops = re.findall(r"while\s*\(true\)", code)
        for l in while_true_loops:
            code = code.replace(l, "while(1)")
        return code

    def preprocess(self, code, features):
        try:
            code = self.remove_comments(code)
            code = self.remove_local_includes(code)
            code = self.remove_preprocess_lines(code)
            code = self.analyze_main(code)
            code = self.remove_verifier_function_definitions(code)
            code = self.remove_verifier_function_declarations(code)
            code = self.replace_nondets_and_assert_assumes(code)
            code = self.apply_patches(code)
            code = self.add_boiler_plate(code)
            code = self.add_frama_c_asserts(code)
            code = self.remove_tmpl(code)
            code = self.clean_newlines(code)
            if self.has_ill_formed_asserts(code):
                raise InvalidBenchmarkException("Ill-formed asserts")

            if self.get_total_loop_count(code) < 1:
                raise InvalidBenchmarkException("No loop found")

            # Filter out benchmarks with multiple methods or loops based on features
            if (not "multiple_methods" in features) and self.is_interprocedural(code):
                raise InvalidBenchmarkException("Found multiple methods")
            if (not "multiple_loops" in features) and self.is_multi_loop(code):
                raise InvalidBenchmarkException("Found multiple loops")

            if (not "arrays" in features) and self.uses_arrays(code):
                raise InvalidBenchmarkException("Found arrays")
            if (not "pointers" in features) and self.uses_pointers(code):
                raise InvalidBenchmarkException("Found pointers")
            # add benchmark specific annotations
            if "multiple_loops" in features:
                code = self.add_loop_labels(code)
        except Exception as e:
            raise InvalidBenchmarkException(str(e))
        return code

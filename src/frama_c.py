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
from llm_utils import Logger


class FramaCChecker(Checker):
    def __init__(self):
        super().__init__("frama-c")
        lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
        self.language = Language(lib_path + "c-tree-sitter.so", "c")
        self.parser = Parser()
        self.parser.set_language(self.language)

    def check(
        self,
        input,
        check_variant=False,
        use_json_dump_for_invariants=False,
        check_contracts=False,
    ):
        temp_file = datetime.datetime.now().strftime(
            "/tmp/temp_eval_%Y_%m_%d_%H_%M_%S_"
        ) + str(random.randint(0, 1000000))
        temp_c_file = temp_file + "_.c"
        temp_wp_json_report_file = temp_file + "_wp_report.json"
        temp_kernel_log_file = temp_file + "_kernel_logs.txt"
        temp_output_dump_file = temp_file + "_output_dump.csv"

        with open(temp_c_file, "w") as f:
            f.write(input)

        cmd = f"frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 \
                -wp-prover=alt-ergo,z3,cvc4 {temp_c_file} -wp-report-json {temp_wp_json_report_file} -kernel-warn-key annot-error=active \
                -kernel-log a:{temp_kernel_log_file} -then -no-unicode -report -report-csv {temp_output_dump_file}"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        frama_c_std_output, err = p.communicate()

        """
        Check kernel log for syntax error line
        """
        if not os.path.exists(temp_kernel_log_file):
            return False, "No kernel logs found"
        with open(temp_kernel_log_file, "r", encoding="utf-8") as f:
            kernel_logs = f.read()
            kl_lines = kernel_logs.splitlines()
            error_line = None
            for line in kl_lines:
                if "[kernel:annot-error]" in line:
                    error_line = line
                    break
                else:
                    continue
            if error_line is not None:
                error_message = self.get_annotation_error_from_kernel_logs(error_line)
                return False, error_message

        checker_output = []
        loop_invariants = []
        user_assertions = []
        loop_variant = ""
        function_contracts = []
        csv_loop_invariants = {}
        success = False

        """
        Get the status of each loop invariant
        """
        if use_json_dump_for_invariants:
            if not os.path.exists(temp_wp_json_report_file):
                return False, "No JSON report found"

            if not os.path.exists(temp_output_dump_file):
                return False, "No CSV output dump found from Frama-C"

            with open(temp_output_dump_file, "r", encoding="utf-8") as f:
                csv_dump = [row for row in csv.DictReader(f, delimiter="\t")]
                csv_loop_invariants = {
                    int(row["line"]): row["status"]
                    for row in csv_dump
                    if row["property kind"] == "loop invariant"
                }

            with open(temp_wp_json_report_file, "r", encoding="utf-8") as f:
                json_output = f.read()
                json_output = re.sub(r"(\d+)\.,", r"\1.0,", json_output)
                json_output = json.loads(json_output)
                loop_invariant_status = {}
                json_invariant_line = {}
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
                        if inv_id[0] not in json_invariant_line:
                            json_invariant_line[inv_id[0]] = item["line"]

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
                        if (
                            json_invariant_line[inv] in csv_loop_invariants
                            and csv_loop_invariants[json_invariant_line[inv]] == "Valid"
                        ):
                            loop_invariants.append(
                                f"loop invariant {invariants_with_ids[inv]} is inductive."
                            )
                        else:
                            loop_invariants.append(
                                f"loop invariant {invariants_with_ids[inv]} is partially proven to be inductive."
                            )
                    elif (
                        not loop_invariant_status[inv]["preserved"]
                        and loop_invariant_status[inv]["established"]
                    ):
                        loop_invariants.append(
                            f"loop invariant {invariants_with_ids[inv]} is established but not preserved."
                        )
                    elif (
                        loop_invariant_status[inv]["preserved"]
                        and not loop_invariant_status[inv]["established"]
                    ):
                        loop_invariants.append(
                            f"loop invariant {invariants_with_ids[inv]} is preserved but not established."
                        )
                    else:
                        loop_invariants.append(
                            f"loop invariant {invariants_with_ids[inv]} is neither established nor preserved."
                        )

                loop_invariants = "\n".join(loop_invariants)

        else:
            # Parse the output dump
            if not os.path.exists(temp_output_dump_file):
                return False, "No CSV output dump found from Frama-C"

            with open(temp_output_dump_file, "r", encoding="utf-8") as f:
                csv_dump = [row for row in csv.DictReader(f, delimiter="\t")]

                success = all(
                    row["status"] == "Valid"
                    for row in checker_output
                    if row["property kind"] == "loop invariant"
                    or row["property kind"] == "user assertion"
                )

                loop_invariants = "\n".join(
                    [
                        f"Invariant {row['property']} on line {row['line']}: {row['status']}"
                        for row in csv_dump
                        if row["property kind"] == "loop invariant"
                    ]
                )

        if not check_variant and not os.path.exists(temp_output_dump_file):
            return False, "No CSV output dump found from Frama-C"

        """
        Get the status of each user assertion and function contract
        """
        with open(temp_output_dump_file, "r", encoding="utf-8") as f:
            csv_dump = [row for row in csv.DictReader(f, delimiter="\t")]

            if check_contracts:
                success = success and all(
                    row["status"] == "Valid"
                    for row in csv_dump
                    if row["property kind"] == "precondition"
                    or row["property kind"] == "postcondition"
                )

                for row in csv_dump:
                    if row["property kind"] == "precondition":
                        function_contracts.append(
                            f"Pre-condition {row['property']} on line {row['line']}: {row['status']}"
                        )
                    elif row["property kind"] == "postcondition":
                        function_contracts.append(
                            f"Post-condition {row['property']} on line {row['line']}: {row['status']}"
                        )

            function_contracts = "\n".join(function_contracts)

            success = success and all(
                row["status"] == "Valid"
                for row in csv_dump
                if row["property kind"] == "user assertion"
            )

            user_assertions = "\n".join(
                [
                    f"Assertion {row['property']}: "
                    + (
                        f"Unproven"
                        if row["status"] == "Unknown"
                        else f"{row['status']}"
                    )
                    for row in csv_dump
                    if row["property kind"] == "user assertion"
                ]
            )

        """
        Check the status of the loop variant
        """
        if check_variant:
            msg = str(frama_c_std_output, "UTF-8").split("\n")
            result = list(filter(lambda x: "Loop variant" in x, msg))
            if len(result) < 1:
                print("No variant found (wrong mode?)")
                return False, "No variant found (wrong mode?)"

            if "Valid" in result[0]:
                loop_variant = "Loop variant is Valid.\n"
                success = success and True
            else:
                loop_variant = "Loop variant is Invalid.\n"
                success = False

        checker_output = (
            loop_invariants
            + "\n"
            + user_assertions
            + "\n"
            + function_contracts
            + "\n"
            + loop_variant
        )
        checker_output = checker_output.strip()

        os.remove(temp_c_file)
        os.remove(temp_wp_json_report_file)
        os.remove(temp_kernel_log_file)
        os.remove(temp_output_dump_file)

        return success, checker_output

    def houdini(self, input_code, features, use_json_dump_for_invariants=False):
        Logger.log_info("Houdini procedure initiated")

        if not self.has_annotations(input_code):
            raise Exception("No annotations found")

        code_queue = [input_code]
        num_frama_c_calls = 0

        while len(code_queue) > 0 and num_frama_c_calls < 100:
            input_code = code_queue.pop(0)
            code_lines = input_code.splitlines()
            if not self.has_annotations(input_code):
                print("No annotations found")
                continue
            success, checker_message = self.check(
                input_code,
                ("termination" in features),
                use_json_dump_for_invariants=use_json_dump_for_invariants,
            )

            if success:
                break

            if (
                "Pre-condition" in checker_message
                or "Post-condition" in checker_message
            ):
                """
                If there are any function contracts, this block will remove "Unknown" clauses from them
                """
                unknown_clause_lines = self.get_line_nums_for_unknown_contract_clauses(
                    checker_message
                )
                for line_no in unknown_clause_lines:
                    code_lines[line_no] = ""

            if "Annotation error " in checker_message:
                # TODO: Why not remove all annotation errors?
                # A: Frama-C panics and skips the entire annotation block
                # as soon as it sees an annotation error.
                # So we get only one annotation error at a time.
                annotation_error_line_no = self.get_line_no_from_error_msg(
                    checker_message
                )[0]

                code_lines[annotation_error_line_no] = ""
                input_code = "\n".join(code_lines)
                code_queue.append(input_code)

            elif use_json_dump_for_invariants:
                non_inductive_invariant_line_nos = (
                    self.get_non_inductive_invariant_line_nos(
                        checker_message, input_code
                    )
                )
                if len(non_inductive_invariant_line_nos) > 0:
                    for line_no in non_inductive_invariant_line_nos:
                        code_lines[line_no] = ""
                    code_queue.append("\n".join(code_lines))

            else:
                # What about TIMEOUT?
                # If any invariant causes a Timeout, it's marked as "Unknown"
                # because the prover could not prove it. So removing it.
                unknown_inv_lines = self.get_unknown_inv_no_from_error_msg(
                    checker_message
                )
                if len(unknown_inv_lines) > 0:
                    for line_no in unknown_inv_lines:
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

                    # for line_no in partially_proven_inv_line_nos:
                    #     code_lines__ = deepcopy(code_lines)
                    #     code_lines__[line_no] = ""
                    #     code_queue.append("\n".join(code_lines__))

            num_frama_c_calls += 1

        if num_frama_c_calls == 100:
            Logger.log_error("Crossed 100 iterations. Stopping pruning...")

        if not success:
            Logger.log_error("Could not find strong enough annotations.")
        else:
            Logger.log_info("Found strong enough annotations.")

        return success, input_code, num_frama_c_calls

    def has_invariant(self, line):
        inv = re.findall(r"loop invariant (.+);", line)
        return len(inv) > 0

    def has_variant(self, line):
        inv = re.findall(r"loop variant (.+);", line)
        return len(inv) > 0

    def has_function_contract(self, lines):
        requires = re.findall(r"requires (.+);", lines)
        ensures = re.findall(r"ensures (.+);", lines)
        return len(requires) > 0 or len(ensures) > 0

    def get_line_nums_for_unknown_contract_clauses(self, checker_message):
        lines = checker_message.splitlines()
        line_numbers = []
        for line in lines:
            if line.startswith("Pre-condition") or line.startswith("Post-condition"):
                line_num = re.findall(r"on line (\d+): (\w+)", line)
                if len(line_num) == 1 and len(line_num[0]) == 2:
                    if line_num[0][1] == "Unknown":
                        line_numbers.append(int(line_num[0][0]) - 1)

        return line_numbers

    def get_annotation_error_from_kernel_logs(self, error_line):
        line_num = re.search(r"\:(\d+)\:", error_line)
        if line_num is not None:
            line_num = int(line_num.group(1))
        error_message = re.search(r"\[kernel\:annot-error\] warning: (.+)", error_line)
        if error_message is not None:
            error_message = error_message.group(1)
        error_message = f"Annotation error on line {line_num}: {error_message}"
        return error_message

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
            if self.has_invariant(lines[int(line_number)]):
                incorrect_invariants.append(lines[int(line_number)].strip())
        return "\n".join(incorrect_invariants)

    def get_invariants(self, lines):
        invariants = []
        invariant_expressions = []
        for line in lines:
            if self.has_invariant(line):
                inv = re.findall(r"(loop invariant (i\d+: )?(.+);)", line)[0]
                if inv[2] not in invariant_expressions:
                    invariants.append(inv[0])
                    invariant_expressions.append(inv[2])
        return invariants

    def get_invariants_with_ids(self, lines):
        invariants = {}
        for line in lines:
            if self.has_invariant(line):
                inv = re.findall(r"loop invariant (\w+:)?(.+);", line)[0]
                invariants[inv[0].rstrip(":")] = inv[1].strip()
        return invariants

    def get_invariants_count(self, code):
        return len(self.get_invariants(code.splitlines()))

    def get_variants(self, lines):
        variants = []
        for line in lines:
            if self.has_variant(line):
                inv = re.findall(r"(loop variant .+;)", line)[0]
                if inv not in variants:
                    variants.append(inv)
        return variants

    def has_annotations(self, code):
        ast = self.parser.parse(bytes(code, "utf-8"))
        comment_query = self.language.query(
            """
            (comment) @comment 
            """
        )
        comments = comment_query.captures(ast.root_node)
        annotations = list(
            filter(lambda x: x[0].text.decode("utf-8").startswith("/*@"), comments)
        )
        annotation_texts = [
            x[0].text.decode("utf-8")[3:-2].strip() for x in annotations
        ]
        annotation_texts = "".join(annotation_texts)

        return len(annotation_texts) > 0

    def get_variant_expressions(self, completions):
        variants = []
        for c in completions:
            c_variant = []
            for line in c.split("\n"):
                if self.has_variant(line):
                    inv = re.findall(r"loop variant (.+);", line)[0]
                    if inv not in c_variant:
                        c_variant.append(inv)
            if len(c_variant) > 0 and c_variant not in variants:
                variants.append(c_variant)
        return variants

    def get_non_inductive_invariant_line_nos(self, checker_message, checker_input):
        lines = checker_message.splitlines()
        non_inductive_invariants = []
        for line in lines:
            if (
                "is inductive." in line
                or "is partially proven to be inductive." in line
            ):
                continue
            else:
                inv_exp = re.findall(r"loop invariant (.+) is", line)
                if len(inv_exp) == 1:
                    non_inductive_invariants.append(inv_exp[0])

        non_inductive_invariant_line_nos = []
        for i, line in enumerate(checker_input.splitlines()):
            if self.has_invariant(line):
                for inv in non_inductive_invariants:
                    inv_match = re.findall(r"loop invariant (\w+: )?(.+);", line)
                    if (
                        len(inv_match) == 1
                        and len(inv_match[0]) == 2
                        and inv_match[0][1] == inv
                    ):
                        non_inductive_invariant_line_nos.append(i)
                        break

        return non_inductive_invariant_line_nos


class FramaCBenchmark(Benchmark):
    def __init__(self, benchmarks_file="", features=None):
        super().__init__(benchmarks_file, features)
        lib_path = os.path.join(os.path.dirname(__file__), "tree_sitter_lib/build/")
        self.language = Language(lib_path + "c-tree-sitter.so", "c")
        self.parser = Parser()
        self.parser.set_language(self.language)
        self.features = features

    def combine_llm_outputs(self, checker_input, llm_outputs, features):
        checker_input_ast = self.parser.parse(bytes(checker_input, "utf-8"))
        root = checker_input_ast.root_node
        loops = self.get_loops(root)
        if self.is_interprocedural(checker_input):
            assert "multiple_methods" in features, "Multiple methods found"
        if len(loops) > 1:
            assert "multiple_loops" in features, "Multiple loops found"

        labels = self.get_labels(checker_input)
        annotations = None
        if len(labels) > 0:
            annotations = {label[1]: "" for label in labels}
            inv_count = 0
            for llm_output in llm_outputs:
                annotation = self.get_annotations(llm_output, labels)
                for label, ann in annotation.items():
                    if label not in annotations:
                        annotations[label] = ""
                    if "Function_" in label:
                        """
                        Find all the requires clauses for this function
                        """
                        requires_clauses = ""
                        if label == "Function_main":
                            requires_clauses = "requires \\true;"
                        else:
                            requires_clauses = []
                            for line in ann.split("\n"):
                                requires = re.findall(r"(requires .+;)", line)
                                if len(requires) > 0:
                                    requires_clauses.append(requires[0])

                            if len(requires_clauses) < 1:
                                new_re = re.compile(r"(requires .+;)", re.MULTILINE)
                                requires_clauses = new_re.findall(ann)
                                if len(requires_clauses) < 1:
                                    requires_clauses = ["requires \\true;"]

                            requires_clauses = "\n".join(requires_clauses)

                        """
                        Find all the ensures clauses for this function
                        """
                        ensures_clauses = []
                        for line in ann.split("\n"):
                            ensures = re.findall(r"(ensures .+;)", line)
                            if len(ensures) > 0:
                                ensures_clauses.append(ensures[0])

                        if len(ensures_clauses) < 1:
                            new_re = re.compile(r"(ensures .+;)", re.MULTILINE)
                            ensures_clauses = new_re.findall(ann)
                            if len(ensures_clauses) < 1:
                                ensures_clauses = ["ensures \\true;"]

                        ensures_clauses = "\n".join(ensures_clauses)

                        old_annotation = annotations[label]
                        annotations[label] = (
                            requires_clauses
                            + "\n"
                            + old_annotation
                            + "\n"
                            + ensures_clauses
                        )
                    else:
                        invariants = {}
                        for line in ann.split("\n"):
                            invariant = re.findall(r"loop invariant (.+);", line)
                            if len(invariant) > 0:
                                inv_id = re.findall(r"loop invariant (\w+:) ", line)
                                if len(inv_id) > 0:
                                    invariant = [invariant[0].replace(inv_id[0], "")]
                                invariant = f"loop invariant i{inv_count + 1}: {invariant[0]};"  # add loop invariant label
                                invariants[invariant] = True
                                inv_count += 1

                        annotations[label] = (
                            annotations[label]
                            + "\n"
                            + "\n".join(list(invariants.keys()))
                        )

            labels = sorted(labels, key=lambda x: x[0][0].start_byte, reverse=True)
            for (node, _), label in labels:
                checker_input = (
                    checker_input[: node.start_byte]
                    + (
                        ""
                        if annotations[label] == ""
                        else "/*@\n" + annotations[label] + "\n*/\n"
                    )
                    + checker_input[node.end_byte :]
                )

            return checker_input

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
            if len(llm_outputs) < 2:
                raise Exception(
                    "Inputs should be inductive invariants and possible variants"
                )

            annotated_candidates = []
            invariants = llm_outputs[0]
            inv_count = 0

            loop = self.get_loops(self.get_main_definition(checker_input))
            if len(loop) != 1:
                raise Exception(
                    "No singular loop found while adding annotations. Multiple loops not supported yet."
                )
            loop = loop[0]

            for llm_output in llm_outputs[1]:
                variants = {}
                for line in llm_output.split("\n"):
                    __variants = re.findall(r"(loop variant .+;)", line)

                    for variant in __variants:
                        variants[variant] = True

                if len(variants) == 0:
                    continue

                elif len(variants) > 1:
                    annotated_candidate = self.generate_lexicographic_variants(
                        checker_input=checker_input,
                        invariants=invariants,
                        variants=llm_output,
                    )
                    annotated_candidates.append(annotated_candidate)

                else:
                    variant = list(variants.keys())[0]
                    annotated_candidates.append(
                        checker_input[: loop.start_byte]
                        + "/*@\n"
                        + invariants
                        + "\n"
                        + variant
                        + "\n*/\n"
                        + checker_input[loop.start_byte :]
                    )

            return annotated_candidates

        elif "one_loop_one_method" in features:
            invariants = []
            invariant_expressions = {}
            inv_count = 0
            for llm_output in llm_outputs:
                lines = llm_output.splitlines()
                for line in lines:
                    invariant = re.findall(r"loop invariant (.+);", line)
                    if len(invariant) > 0:
                        inv_id = re.findall(
                            r"loop invariant ([a-zA-Z_][a-zA-Z_0-9]*:\s*)", line
                        )
                        if len(inv_id) > 0:
                            line = line.replace(
                                "loop invariant " + inv_id[0], "loop invariant "
                            )
                            invariant = re.findall(r"loop invariant (.+);", line)
                        if invariant[0] not in invariant_expressions:
                            invariant_expressions[invariant[0]] = True
                            invariant = f"loop invariant i{inv_count + 1}: {invariant[0]};"  # add loop invariant label
                            invariants.append(invariant)
                            inv_count += 1

            loop = self.get_loops(self.get_main_definition(checker_input))
            if len(loop) != 1:
                raise Exception("No singular loop found while adding annotations")
            loop = loop[0]
            output = (
                checker_input[: loop.start_byte]
                + "/*@\n"
                + "\n".join(invariants)
                + "\n*/\n"
                + checker_input[loop.start_byte :]
            )

            return output

        else:
            raise Exception("Unknown feature set")

    def get_annotations(self, code_block, labels):
        """
        Returns all the annotations in the code block
        """
        annotations = {}
        for label in labels:
            annotation = ""
            begin = re.findall(r"<\s*" + label[1] + r"\s*>", code_block)
            end = re.findall(r"<\s*/\s*" + label[1] + r"\s*>", code_block)
            if len(begin) == 1 and len(end) == 1:
                annotation = code_block[
                    code_block.find(begin[0]) + len(begin[0]) : code_block.find(end[0])
                ]
            else:
                print("Ill-formatted annotation found")
                continue
            annotations[label[1]] = annotation

        return annotations

    def get_labels(self, code):
        """
        This has to be called only on code that
        has been passed through the parser because
        ths assumes comments to be ACSL asserts or labels
        """
        labels = {}
        ast = self.parser.parse(bytes(code, "utf-8"))
        comment_query = self.language.query(
            """
            (comment) @comment 
            """
        )
        comments = comment_query.captures(ast.root_node)
        comments = list(
            filter(lambda x: not x[0].text.decode("utf-8").startswith("//@"), comments)
        )
        comments = sorted(comments, key=lambda x: x[0].start_byte, reverse=True)

        labels = []
        for comment in comments:
            comment_text = re.findall(r"\/\*(.+)\*\/", comment[0].text.decode("utf-8"))
            comment_text = comment_text[0].strip()
            labels.append((comment, comment_text))

        return labels

    def generate_lexicographic_variants(self, checker_input, invariants, variants):
        # Assume all the variant expressions are unique
        variant_expressions = []
        for line in variants.split("\n"):
            variant = re.findall(r"loop variant (.+);", line)
            if len(variant) > 0:
                variant_expressions.append(variant[0])

        num_variants = len(variant_expressions)

        if num_variants == 0:
            return checker_input

        # Generate a struct for the variant expressions
        struct_string = """
        typedef struct {
        """
        for i in range(num_variants):
            struct_string += f"int {chr(i + 97)};\n"
        struct_string += "} variant_expression;\n"

        # Generate the lexicographic predicate
        predicate_string = """/*@ 
            predicate lexicographic(variant_expression v1, variant_expression v2) =
        """
        disjuncts = []
        for i in range(num_variants):
            conjunct_1 = f"v1.{chr(i + 97)} >= 0"
            equality_conjunct_1 = " && ".join(
                [f"v1.{chr(j + 97)} == v2.{chr(j + 97)}" for j in range(i)]
            )
            inequality_conjunct_1 = f"v1.{chr(i + 97)} > v2.{chr(i + 97)}"

            disjunct = (
                conjunct_1
                + ((" && " + equality_conjunct_1) if equality_conjunct_1 != "" else "")
                + " && "
                + inequality_conjunct_1
            )
            disjunct = "(" + disjunct + ")"
            disjuncts.append(disjunct)

        predicate_string += " ||\n ".join(disjuncts) + ";\n*/"

        annotated_checker_input = (
            struct_string + "\n" + predicate_string + "\n" + checker_input
        )

        # Generate ghost variable declaration
        ghost_var_string = (
            """//@ ghost variant_expression measure = { """
            + ", ".join(variant_expressions)
            + " };\n"
        )

        # Generate ghost variable loop invariant
        ghost_inv_string = (
            "loop invariant "
            + " && ".join(
                [
                    f"measure.{chr(i + 97)} == {variant_expressions[i]}"
                    for i in range(num_variants)
                ]
            )
            + ";"
        )
        invariants = invariants + "\n" + ghost_inv_string

        # Generate ghost variable assignments
        ghost_assign_string = "\n".join(
            [
                f"//@ ghost measure.{chr(i + 97)} = {variant_expressions[i]};"
                for i in range(num_variants)
            ]
        )

        loop = self.get_loops(self.get_main_definition(annotated_checker_input))
        if len(loop) != 1:
            raise Exception(
                "No singular loop found while adding annotations. Multiple loops not supported yet."
            )
        loop = loop[0]

        annotated_code_with_variants = (
            annotated_checker_input[: loop.start_byte]
            + ghost_var_string
            + "/*@\n"
            + invariants
            + "\n"
            + "loop variant measure for lexicographic;"
            + "\n*/\n"
            + annotated_checker_input[loop.start_byte :]
        )

        loop = self.get_loops(self.get_main_definition(annotated_code_with_variants))
        loop = loop[0]

        annotated_code_with_variants_and_ghost_variables = (
            annotated_code_with_variants[: loop.end_byte - 1]
            + "\n"
            + ghost_assign_string
            + "\n"
            + annotated_code_with_variants[loop.end_byte - 1 :]
        )

        return annotated_code_with_variants_and_ghost_variables

    def is_invariant(self, line):
        inv = re.findall(r"loop invariant (.+);", line)
        return len(inv) > 0

    def is_variant(self, line):
        inv = re.findall(r"loop variant (.+);", line)
        return len(inv) > 0

    def extract_loop_invariants(self, code):
        loop_invariants = []
        ast = self.parser.parse(bytes(code, "utf-8"))
        comment_query = self.language.query(
            """
            (comment) @comment 
            """
        )
        comments = comment_query.captures(ast.root_node)
        comments = list(
            filter(lambda x: x[0].text.decode("utf-8").startswith("/*@"), comments)
        )

        if len(comments) > 1:
            raise Exception("More than 1 loop annotation found")

        comment = comments[0][0]
        comment = code[comment.start_byte : comment.end_byte]

        for line in comment.split("\n"):
            if self.is_invariant(line):
                loop_invariants.append(line)
        return "\n".join(loop_invariants)

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
        """
        Add hash defines and externs for unknown functions
        """
        ast = self.parser.parse(bytes(code, "utf-8"))

        main_definition = self.get_main_definition(code)
        main_definition_type = main_definition.child_by_field_name("type")

        code = (
            (
                "#define assume(e) if(!(e)) return;\n"
                if main_definition_type.text.decode("utf-8") == "void"
                else "#define assume(e) if(!(e)) return 0;\n"
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

    def error_label_to_frama_c_assert(self, code):
        # get main function
        ast = self.parser.parse(bytes(code, "utf-8"))
        root = ast.root_node
        if not "multiple_methods" in self.features:
            root = self.get_main_definition(code)

        # catch ERROR: in main
        errors = self.get_error_labels(root)
        errors = sorted(errors, key=lambda x: x.start_byte, reverse=True)
        for e in errors:
            code = (
                code[: e.start_byte]
                + "{ ERROR: {; \n//@ assert(\\false);\n}\n}"
                + code[e.end_byte :]
            )

        return code

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

    def apply_patches(self, code):
        """
        Miscellaneous patches to fix benchmarks.
        Frama-C panics on seeing while(true) without stdbool.
        tmpl() is not supported by Frama-C.
        """
        while_true_loops = re.findall(r"while\s*\(true\)", code)
        for l in while_true_loops:
            code = code.replace(l, "while(1)")

        lines = code.split("\n")
        lines = list(map(lambda x: re.sub(r"tmpl\s*\(.*\)\s*;", "", x), lines))
        return "\n".join(lines)

        return code

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
            if function_call[1] == "reach_error":
                code = (
                    code[: function_call[0].start_byte]
                    + "{; \n//@ assert(\\false);\n}"
                    + code[function_call[0].end_byte :]
                )

        return code

    def add_method_label(self, code):
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

    def preprocess(self, code, features, max_lines=500):
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
            code = self.error_label_to_frama_c_assert(code)
            code = self.remove_reach_error_calls(code)
            code = self.clean_newlines(code)

            """
            Remove unqualified benchmarks
            """
            if self.has_ill_formed_asserts(code):
                raise InvalidBenchmarkException("Ill-formed asserts")

            # return (
            #     self.get_total_loop_count(code),
            #     self.is_interprocedural(code),
            #     self.uses_arrays(code),
            #     self.uses_pointers(code),
            #     len(code.splitlines()),
            # )

            if self.get_total_loop_count(code) < 1 and not self.is_interprocedural(
                code
            ):
                raise InvalidBenchmarkException(
                    "No loop found. Cannot infer loop invariants"
                )
            """
            We do not support benchmarks with arrays or pointers.
            """
            if (not "arrays" in features) and self.uses_arrays(code):
                raise InvalidBenchmarkException("Found arrays")
            if (not "pointers" in features) and self.uses_pointers(code):
                raise InvalidBenchmarkException("Found pointers")

            """
            Add labels or raise exception depending on the features set
            """
            if "multiple_methods" in features:
                code = self.add_method_label(code)
            elif self.is_interprocedural(code):
                raise InvalidBenchmarkException("Found multiple methods")

            if "multiple_loops" in features:
                code = self.add_loop_labels(code)
            elif self.is_multi_loop(code):
                raise InvalidBenchmarkException("Found multiple loops")

            # if not (
            #     self.is_interprocedural(code) or self.get_total_loop_count(code) > 1
            # ):
            #     raise InvalidBenchmarkException("Not for SV-COMP benchmark set")

            num_lines = len(code.splitlines())
            if num_lines > max_lines:
                raise InvalidBenchmarkException(
                    f"Number of lines ({num_lines}) exceeded max_lines ({max_lines})"
                )

        except Exception as e:
            raise InvalidBenchmarkException(str(e))
        return code

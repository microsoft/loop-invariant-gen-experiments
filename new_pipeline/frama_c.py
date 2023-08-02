import csv
import os
import re
import subprocess
from copy import deepcopy
import datetime
import random
import sys

from benchmark import Benchmark
from checker import Checker

err_json = False

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

    def check(self, input, mode="invariant", verbose=False):
        temp_file = datetime.datetime.now().strftime(
            "/tmp/temp_eval_%Y_%m_%d_%H_%M_%S_"
        ) + str(random.randint(0, 1000000))
        temp_c_file = temp_file + "_.c"
        temp_kernel_log_file = temp_file + "_kernel_logs.txt"
        temp_output_dump_file = temp_file + "_output_dump.json"
        temp_output_dump_file2 = temp_file + "_output_dump2.json"

        with open(temp_c_file, "w") as f:
            f.write(input)

        if verbose:
            print("==============================")
        cmd = "frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 10 -wp-prover=alt-ergo,z3,cvc4 {temp_c_file} -wp-report-json {temp_output_dump_file} \
                -kernel-warn-key annot-error=active -kernel-log a:{temp_kernel_log_file} -then -report -report-classify \
                -report-output {temp_output_dump_file2}" if err_json else f"frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 \
                -wp-prover=alt-ergo,z3,cvc4 {temp_c_file} -kernel-warn-key annot-error=active \
                -kernel-log a:{temp_kernel_log_file} -then -no-unicode -report -report-csv {temp_output_dump_file}"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()

        # Look for errors in the kernel logs
        if not os.path.exists(temp_kernel_log_file):
            return False, "No kernel logs found"
        with open(temp_kernel_log_file, "r", encoding="utf-8") as f:
            kernel_logs = f.read()
            print(kernel_logs)
            kl_lines = kernel_logs.splitlines()
            if len(kl_lines) > 2:
                print("More than 2 lines in Frama-C kernel logs.")
            error_line = None
            for line in kl_lines:
                if "[kernel:annot-error]" in line:
                    error_line = line
                    break
                else:
                    continue
            if error_line is not None:
                error_message = self.get_annotation_error_from_kernel_logs(error_line)
                if " unexpected token ''" in error_message:
                    error_message = "No invariants found."
                return False, error_message

        # Parse the output dump
        if mode == "invariant" and not os.path.exists(temp_output_dump_file):
            return False, "No output dump found"

        csv_output = None
        success = True
        if err_json:
            # TODO: handle the json output, but it seems buggy
            with open(temp_output_dump_file, "r") as errfile:
                outmsg = json.load(errfile)
                print(outmsg)
        else:
            with open(temp_output_dump_file, "r", encoding="utf-8") as f:
                csv_output = [row for row in csv.DictReader(f, delimiter="\t")]
                success = all(
                    row["status"] == "Valid"
                    for row in csv_output
                    if row["property kind"] == "loop invariant"
                    or row["property kind"] == "user assertion"
                )

                user_assertion = "\n".join(
                    [
                        f"Post-condition {row['property']} on line {row['line']}: {row['status']}"
                        for row in csv_output
                        if row["property kind"] == "user assertion"
                    ]
                )

                csv_output = "\n".join(
                    [
                        f"Invariant {row['property']} on line {row['line']}: {row['status']}"
                        for row in csv_output
                        if row["property kind"] == "loop invariant"
                    ]
                )
                csv_output = csv_output + "\n" + user_assertion + "\n"
            if mode == "variant":
                msg = str(output, "UTF-8").split("\n")
                result = list(filter(lambda x: "Loop variant" in x, msg))
                assert len(result) == 1
                if "Valid" in result[0]:
                    csv_output += "Loop variant is Valid"
                    success = success and True
                else:
                    csv_output += "Loop variant is Invalid"
                    success = False

        os.remove(temp_c_file)
        os.remove(temp_kernel_log_file)
        os.remove(temp_output_dump_file)
        return success, csv_output

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
        for line in lines:
            if self.is_invariant(line):
                inv = re.findall(r"(loop invariant .+;)", line)[0]
                if inv not in invariants:
                    invariants.append(inv)
        return invariants

    def get_invariants_count(self, code):
        return len(self.get_invariants(code.splitlines()))

    def get_variants(self, lines):
        invariants = []
        for line in lines:
            if self.is_variant(line):
                inv = re.findall(r"(loop variant .+;)", line)[0]
                if inv not in invariants:
                    invariants.append(inv)
        return invariants

    def prune_annotations_and_check(self, input_code, mode="invariant", verbose=False):
        print("Pruning annotations...")
        getf = None
        if mode == "invariant":
            get_f = self.get_invariants
            is_f = self.is_invariant
        else:
            get_f = self.get_variants
            is_f = self.is_variant
        invariant_line_mapping = {}
        lines = input_code.splitlines()
        for no, line in enumerate(lines):
            if is_f(line):
                invariant_line_mapping[no] = line
        if len(invariant_line_mapping) == 0:
            raise Exception("No invariants/variants found")

        inv_line_list = list(invariant_line_mapping.keys())
        (invariant_line_start, invariant_line_end) = (
            inv_line_list[0],
            inv_line_list[-1],
        )

        input_code = "\n".join(
            lines[:invariant_line_start]
            + get_f(lines)
            + lines[invariant_line_end + 1 :]
        )
        code_queue = [input_code]
        iterations = 0

        while len(code_queue) > 0 and iterations < 1000:
            input_code = code_queue.pop(0)
            code_lines = input_code.splitlines()
            if len(get_f(code_lines)) == 0:
                print("No invariants/variants found")
                continue
            status, checker_message = self.check(input_code, mode, verbose)

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
                code_lines[annotation_error_line_no] = ""
                input_code = "\n".join(code_lines)
                code_queue.append(input_code)
            else:
                # TODO: What about TIMEOUT?
                # If any invariant causes a Timeout, it's marked as "Unknown"
                # because the prover could not prove it. So removing it for now.
                # Remove all "Unknown" invariants
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
            iterations += 1

        if iterations == 1000:
            print("Crossed 1000 iterations. Stopping pruning...")

        if not status:
            print(
                "Invariants/variant not strong enough to prove or benchmark is invalid."
            )
        else:
            print("Found strong enough invariants/variant.")

        return status, input_code


class FramaCBenchmark(Benchmark):
    def __init__(self, llm_input_dir=None, checker_input_dir=None):
        super().__init__(llm_input_dir, checker_input_dir)

    def combine_llm_outputs(self, checker_input, llm_outputs, mode="invariant"):
        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                invariant = re.findall(r"(loop invariant .+;)", line)
                if len(invariant) == 0 and mode == "variant":
                    invariant = re.findall(r"(loop variant .+;)", line)
                if len(invariant) > 0:
                    invariants.append(invariant[0])

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            while_re = re.findall(r"while\s*\((.+)\)", line)
            for_re = re.findall(r"for\s*\(", line)
            if len(while_re) > 0 or len(for_re) > 0:
                loc = index
                break
        if loc is not None:
            lines = (
                lines[:loc]
                + ((["/*@\n"] + invariants + ["\n*/"]) if len(invariants) > 0 else [""])
                + lines[loc:]
            )
        else:
            raise Exception("No while loop found")
        output = "\n".join(lines)

        return output

    def fix_void_main(self, code):
        void_main_returning_nothing = re.findall(
            r"void \w+\(((.|\n|\t)*)*(return;)", code
        )
        while len(void_main_returning_nothing) > 0:
            code.replace(void_main_returning_nothing[0][2], "return 0;")
            void_main_returning_nothing = re.findall(
                r"void \w+\(((.|\n|\t)*)*(return;)", code
            )
        return code

    def fix_int_main(self, code):
        int_main_returning_nothing = re.findall(
            r"int \w+\(((.|\n|\t)*)*(return;)", code
        )
        while len(int_main_returning_nothing) > 0:
            code.replace(int_main_returning_nothing[0][2], "return 0;")
            int_main_returning_nothing = re.findall(
                r"int \w+\(((.|\n|\t)*)*(return;)", code
            )
        return code

    def raw_input_to_checker_input(self, code):
        lines = code.splitlines()
        new_code = ""
        int_main = False
        void_main = False
        inside_main = False
        for line in lines:
            # Replace return with return 0 if main returns int
            if "int main" in line:
                int_main = True
            if len(re.findall(r"return\s*;", line)) > 0 and int_main:
                line = line.replace("return", "return 0;")
            if "void main" in line:
                void_main = True
            if len(re.findall(r"return\s+[a-zA-Z0-9_]+;", line)) > 0 and void_main:
                line = line.replace("return", "return;")
            if len(re.findall(r"main\s*\(", line)):
                inside_main = True

            # Remove existing annotation-like comments
            if len(re.findall(r"/\*@[^\b\*/]*\*/", line)) > 0:
                line = re.sub(r"/\*@[^\b\*/]*\*/", "", line)

            # Remove pre-processor directives
            if re.match(r"#\s+\d+\s+\"[^\"]*\"[\s\d]*", line):
                continue

            # Remove all local assert header files
            if len(re.findall(r"#include\s+\".*\"", line)) > 0:
                continue

            if (
                len(
                    re.findall(
                        r"(extern\s)?\s*[int|char|_Bool|void]\s+__VERIFIER_[^\(]*(.*);",
                        line,
                    )
                )
                > 0
            ):
                continue

            # Convert ERROR: to assert(\false)
            if "ERROR:" in line and inside_main:
                error_text = re.findall(r"ERROR:(.*)", line)[0]
                if len(error_text) > 0:
                    line = line.replace("ERROR:", "ERROR: //@ assert(\\false);\n")

            # Remove local nondet functions
            elif "__VERIFIER_nondet_" in line:
                if "__VERIFIER_nondet_int" in line:
                    line = line.replace("__VERIFIER_nondet_int", "unknown_int")
                if "__VERIFIER_nondet_uint" in line:
                    line = line.replace("__VERIFIER_nondet_uint", "unknown_uint")
                if "__VERIFIER_nondet_bool" in line:
                    line = line.replace("__VERIFIER_nondet_bool", "unknown_bool")
                if "__VERIFIER_nondet_char" in line:
                    line = line.replace("__VERIFIER_nondet_char", "unknown_char")
                if "__VERIFIER_nondet_ushort" in line:
                    line = line.replace("__VERIFIER_nondet_ushort", "unknown_ushort")
            elif "nondet" in line:
                line = line.replace("nondet", "unknown")

            # Remove local assume function
            elif "__VERIFIER_assume" in line:
                assuming_conditions = re.findall(
                    r"(__VERIFIER_assume\s*\((.+)\);)", line
                )
                for condition in assuming_conditions:
                    line = line.replace(condition[0], "assume(" + condition[1] + ");\n")

            # Remove local assert function
            elif "__VERIFIER_assert" in line:
                asserting_conditions = re.findall(
                    r"^(?!\s*//).*(__VERIFIER_assert\((.+)\);)", line
                )
                for condition in asserting_conditions:
                    line = line.replace(
                        condition[0], "{; //@ assert(" + condition[1] + ");\n}\n"
                    )

            elif (
                len(re.findall(r"[^s]assert\s*\([^{}]*\);", line)) > 0
                and len(re.findall(r"extern\s+\w+\s+assert\s*\([^{}]*\);", line)) == 0
                and len(
                    re.findall(
                        r"\bvoid\s+reach_error\(\)\s+\{\s+assert\(0\);\s+\}", line
                    )
                )
                == 0
                and len(re.findall(r"//\s*assert\s*\([^{}]*\);", line)) == 0
            ):
                assertion = line.strip()
                line = line.replace(assertion, "{; //@ " + assertion + "\n}\n")

            elif len(re.findall(r"sassert\s*\(.*\);", line)) > 0:
                line = line.replace("sassert", "assert")
                assertion = line.strip()
                line = line.replace(assertion, "{; //@ " + assertion + "\n}\n")

            if "tmpl(" in line:
                line = "// " + line

            if len(re.findall(r"__VERIFIER_error\s*\(\);", line)) > 0:
                line = re.sub(r"__VERIFIER_error\s*\(\);", ";", line)

            new_code += line + "\n"
        new_code = (
            (
                "#define assume(e) if(!(e)) return;"
                if void_main
                else "#define assume(e) if(!(e)) return 0;"
            )
            + ("\n#define LARGE_INT 1000000" if "LARGE_INT" in code else "")
            + """

extern int unknown(void);
extern int unknown_int(void);
extern unsigned int unknown_uint(void);
extern _Bool unknown_bool(void);
extern char unknown_char(void);
extern unsigned short unknown_ushort(void);
"""
            + "".join(new_code)
        )
        return new_code

    def add_loop_ids(self, code):
        return ""

    def preprocess(self, code):
        code0 = self.remove_comments(code)
        code1 = self.raw_input_to_checker_input(code0)
        code2, loop_list = self.add_loop_ids(code1)
        return code2, loop_list

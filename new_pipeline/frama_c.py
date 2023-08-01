import csv
import os
import re
import subprocess
from copy import deepcopy

from benchmark import Benchmark
from checker import Checker


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

    def check(self, input, verbose=False):
        with open("/tmp/temp_eval.c", "w") as f:
            f.write(input)

        if verbose:
            print("==============================")
        cmd = "frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 -wp-prover=alt-ergo,z3,cvc4 /tmp/temp_eval.c -kernel-warn-key annot-error=active \
            -kernel-log a:/tmp/frama_c_kernel_logs.txt -then -no-unicode -report -report-csv /tmp/frama_c_eval.csv"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()

        # Look for errors in the kernel logs
        if not os.path.exists("/tmp/frama_c_kernel_logs.txt"):
            return False, "No kernel logs found"
        with open("/tmp/frama_c_kernel_logs.txt", "r", encoding="utf-8") as f:
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
        if not os.path.exists("/tmp/frama_c_eval.csv"):
            return False, "No output dump found"

        with open(f"/tmp/frama_c_eval.csv", "r", encoding="utf-8") as f:
            csv_output = [row for row in csv.DictReader(f, delimiter="\t")]
            print(csv_output)
            success = all(
                row["status"] == "Valid"
                for row in csv_output
                if row["property kind"] == "loop invariant"
            ) and any(
                row["property kind"] == "user assertion" and row["status"] == "Valid"
                for row in csv_output
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
            csv_output = csv_output + "\n" + user_assertion

        os.remove("/tmp/temp_eval.c")
        os.remove("/tmp/frama_c_kernel_logs.txt")
        os.remove("/tmp/frama_c_eval.csv")
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
        checked_already = [input_code]

        while len(code_queue) > 0:
            input_code = code_queue.pop(0)
            code_lines = input_code.splitlines()
            if len(get_f(code_lines)) == 0:
                print("No invariants/variants found")
                continue
            status, checker_message = self.check(input_code, verbose)

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
                    if verbose:
                        if len(partially_proven_inv_line_nos) > 0:
                            print("Forking: All partially proven invariants.")
                        else:
                            print("No partially proven invariant")

                    for line_no in partially_proven_inv_line_nos:
                        code_lines__ = deepcopy(code_lines)
                        code_lines__[line_no] = ""
                        code_queue.append("\n".join(code_lines__))

        if not status:
            print("Invariants not strong enough to prove")
        else:
            print("Found strong enough invariants")

        return status, input_code


class FramaCBenchmark(Benchmark):
    def __init__(self, llm_input_dir=None, checker_input_dir=None):
        super().__init__(llm_input_dir, checker_input_dir)

    def combine_llm_outputs(self, checker_input, llm_outputs, mode='invariant'):
        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                if mode == "invariant":
                    invariant = re.findall(r"(loop invariant .+;)", line)
                else:
                    invariant = re.findall(r"(loop variant .+;)", line)
                if len(invariant) > 0:
                    invariants.append(invariant[0])

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            while_re = re.findall(r"while\s*\((.+)\)", line)
            for_re = re.findall(r"for\s*\((.+)\)", line)
            if len(while_re) > 0 or len(for_re) > 0:
                loc = index
                break
        if loc is not None:
            lines = (
                lines[:loc]
                + ((["/*@\n"] + invariants + ["\n*/"]) if len(invariants) > 0 else [""])
                + lines[loc :]
            )
        else:
            raise Exception("No while loop found")
        output = "\n".join(lines)

        return output

    def raw_input_to_checker_input(self, code):
        lines = code.splitlines()
        new_code = ""
        int_main = False
        for line in lines:
            # Replace return with return 0 if main returns int
            if "int main" in line:
                int_main = True
            if "return;" in line and int_main:
                line = line.replace("return;", "return 0;")

            # Remove all local assert header files
            if "#include \"myassert.h\"" in line or "#include \"assert.h\"" in line:
                continue

            # Convert ERROR: to assert(\false)
            if "ERROR:" in line:
                error_text = re.findall(r"ERROR:(.+)", line)[0]
                if len(error_text) > 0:
                    line = line.replace("ERROR:", "ERROR: //@ assert(\\false);\n")

            # Remove local nondet functions
            elif "__VERIFIER_nondet_int" in line:
                line = line.replace("__VERIFIER_nondet_int", "unknown_int")
            elif "__VERIFIER_nondet_uint" in line:
                line = line.replace("__VERIFIER_nondet_uint", "unknown_uint")
            elif "__VERIFIER_nondet_bool" in line:
                line = line.replace("__VERIFIER_nondet_bool", "unknown_bool")
            elif "__VERIFIER_nondet_char" in line:
                line = line.replace("__VERIFIER_nondet_char", "unknown_char")
            elif "__VERIFIER_nondet_ushort" in line:
                line = line.replace("__VERIFIER_nondet_ushort", "unknown_ushort")
            elif "nondet" in line:
                line = line.replace("nondet", "unknown")
            
            # Remove local assume function
            elif "__VERIFIER_assume" in line:
                assuming_conditions = re.findall(
                    r"(__VERIFIER_assume\(([^\(\)]+)\);)", line
                )
                for condition in assuming_conditions:
                    line = line.replace(condition[0], "assume(" + condition[1] + ");\n")
            
            # Remove local assert function
            elif "__VERIFIER_assert" in line:
                asserting_conditions = re.findall(
                    r"(__VERIFIER_assert\(([^\(\)]+)\);)", line
                )
                for condition in asserting_conditions:
                    line = line.replace(
                        condition[0], "//@ assert(" + condition[1] + ");\n"
                    )
            
            elif "assert" in line and not "//assert" in line:
                assertion = line.strip()
                line = line.replace(assertion, "{;\n //@ " + assertion + "\n}")

            new_code += line + "\n"
        new_code = """#define assume(e) if(!(e)) return 0;

extern int unknown(void);
extern int unknown_int(void);
extern unsigned int unknown_uint(void);
extern _Bool unknown_bool(void);
extern char unknown_char(void);
extern unsigned short unknown_ushort(void);
""" + "".join(
            new_code
        )
        return new_code

import csv
import os
import re
import subprocess

from benchmark import Benchmark
from checker import Checker


class FramaCChecker(Checker):
    def __init__(self):
        super().__init__("frama-c")

    def is_invariant(self, line):
        return "loop invariant " in line

    def get_annotation_error_from_kernel_logs(self, error_line):
        line_num = re.search(r"\:(\d+)\:", error_line)
        if line_num is not None:
            line_num = int(line_num.group(1))
        error_message = re.search(r"\[kernel\:annot-error\] warning: (.+)", error_line)
        if error_message is not None:
            error_message = error_message.group(1)
        error_message = f"Annotation error on line {line_num}: {error_message}"
        return error_message

    def check(self, input):
        with open("/tmp/temp_eval.c", "w") as f:
            f.write(input)

        cmd = "frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 -wp-prover=alt-ergo,z3,cvc4 /tmp/temp_eval.c -kernel-warn-key annot-error=active \
            -kernel-log a:/tmp/frama_c_kernel_logs.txt -then -report -report-csv /tmp/frama_c_eval.csv"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()

        # Look for errors in the kernel logs
        with open("/tmp/frama_c_kernel_logs.txt", "r", encoding="utf-8") as f:
            kernel_logs = f.read()
            kl_lines = kernel_logs.splitlines()
            if len(kl_lines) > 2:
                print(
                    "Didn't expect more than 2 lines in Frama-C kernel logs. \
                        Proceeding anyway. Hopefully it's fine."
                )
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

        # Parse the output dump
        with open(f"/tmp/frama_c_eval.csv", "r", encoding="utf-8") as f:
            csv_output = [row for row in csv.DictReader(f, delimiter="\t")]
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
        pattern = r"on line (\d+): [^Valid|Partially proven]"
        matches = re.findall(pattern, checker_output)
        line_numbers = [int(match) - 1 for match in matches]

        return line_numbers


class FramaCBenchmark(Benchmark):
    def __init__(self, llm_input_dir=None, checker_input_dir=None):
        super().__init__(llm_input_dir, checker_input_dir)

    def combine_llm_outputs(self, checker_input, llm_outputs):
        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                invariant = re.findall(r"(loop invariant .+;)", line)
                if len(invariant) > 0:
                    invariants.append(invariant[0])

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "while" in line:
                loc = index - 1
                break
        if loc is not None:
            lines = (
                lines[:loc]
                + ((["/*@\n"] + invariants + ["\n*/"]) if len(invariants) > 0 else [""])
                + lines[loc + 1 :]
            )
        else:
            raise Exception("No while loop found")
        output = "\n".join(lines)

        return output

    def raw_input_to_checker_input(self, code):
        lines = code.splitlines()
        new_code = ""
        for line in lines:
            if "assert" in line and not "//assert" in line:
                assertion = line.strip()
                line = line.replace(assertion, "{;\n //@ " + assertion + "\n}")
            new_code += line + "\n"
        new_code = (
            """#define assume(e) if(!(e)) return 0;\nextern int unknown(void);\n"""
            + "".join(new_code)
        )
        return new_code
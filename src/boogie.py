"""
This is experimental code for using Boogie as a checker.
This is just a proof of concept and is not used in the final version.
"""

import os
import re
import subprocess
from datetime import datetime
from benchmark import InvalidBenchmarkException, Benchmark
from checker import Checker
from llm_utils import Logger


class BoogieBenchmark(Benchmark):
    def __init__(self, benchmarks_file="", features=None):
        self.input_benchmarks = os.path.join(
            os.path.dirname(__file__), "../", benchmarks_file
        )
        self.features = features
        self.input_file_paths = []

    def preprocess(self, code):
        raise NotImplementedError

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

    def extract_loop_invariants(self, code):
        raise NotImplementedError


class BoogieChecker(Checker):
    def __init__(self, name="boogie"):
        self.name = name
        self.timeout = 10

    def check(self, code, features):
        with open("/tmp/temp_eval.bpl", "w") as f:
            f.write(code)

        cmd = f"boogie /tmp/temp_eval.bpl /timeLimit:{self.timeout}"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        output = output.decode()

        if "1 verified" in output:
            return True, output
        else:
            return False, output

    def has_invariant(self, line):
        return "invariant" in line

    def has_variant(self, line):
        raise NotImplementedError

    def has_function_contract(self, lines):
        raise NotImplementedError

    def get_line_no_from_error_msg(self, error_string):
        pattern = r"\((\d+),\d+\): Error"
        matches = re.findall(pattern, error_string)
        line_numbers = [int(match) - 1 for match in matches]

        pattern = r"\((\d+),\d+\): error"
        matches = re.findall(pattern, error_string)
        line_numbers2 = [int(match) - 1 for match in matches]
        line_numbers = line_numbers + line_numbers2

        return line_numbers

    def get_incorrect_invariants(self, code, error):
        line_numbers = self.get_line_no_from_error_msg(error)
        lines = code.splitlines()
        incorrect_invariants = []
        for line_number in line_numbers:
            if self.has_invariant(lines[int(line_number)]):
                incorrect_invariants.append(lines[int(line_number)].strip())
        return "\n".join(incorrect_invariants)

    def houdini(self, input_code, features):
        print("Pruning annotations")
        while True:
            status, error_string = self.check(input_code)
            invariant_line_mapping = {}
            lines = input_code.splitlines()
            for no, line in enumerate(lines):
                if self.has_invariant(line):
                    invariant_line_mapping[no] = line
            if len(invariant_line_mapping) == 0:
                raise Exception("No invariants found")

            (invariant_line_start, invariant_line_end) = (
                list(invariant_line_mapping.keys())[0],
                list(invariant_line_mapping.keys())[-1],
            )

            line_numbers = self.get_line_no_from_error_msg(error_string)
            incorrect_invariant_line_numbers = [
                no for no in line_numbers if no in invariant_line_mapping.keys()
            ]
            correct_invariant_line_numbers = [
                i
                for i in list(invariant_line_mapping.keys())
                if i not in incorrect_invariant_line_numbers
            ]

            new_lines = (
                lines[:invariant_line_start]
                + [lines[i] for i in correct_invariant_line_numbers]
                + lines[invariant_line_end + 1 :]
            )
            new_code = "\n".join(new_lines)
            input_code = new_code
            status, _ = self.check(input_code)
            if (
                status
                or len(correct_invariant_line_numbers) == 0
                or len(incorrect_invariant_line_numbers) == 0
            ):
                if len(incorrect_invariant_line_numbers) == 0:
                    print("No incorrect invariants remaining")
                if len(correct_invariant_line_numbers) == 0:
                    print("No correct invariants remaining")
                break

        return status, input_code

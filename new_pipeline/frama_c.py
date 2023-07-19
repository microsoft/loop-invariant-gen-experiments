import csv
import re
import subprocess
from loopy import Checker, Benchmark, LoopyPipeline

class FramaCChecker(Checker):
    def __init__(self):
        super().__init__("frama-c")

    def is_invariant(self, line):
        return "loop invariant " in line

    def check(self, input):
        with open("/tmp/temp_eval.c", "w") as f:
            f.write(input)

        cmd = f'frama-c -wp -wp-verbose 100 -wp-debug 100 -wp-timeout 3 -wp-prover=alt-ergo,z3,cvc4 /tmp/temp_eval.c -then -report -report-csv /tmp/frama_c_eval.csv'
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        with open(f'/tmp/frama_c_eval.csv', 'r', encoding='utf-8') as f:
            csv_output = [row for row in csv.DictReader(f, delimiter='\t')]
            success = all(row['status'] == 'Valid' for row in csv_output)
            csv_output = "\n".join([f"Invariant {row['property']} on line {row['line']}: {row['status']}" for row in csv_output if row['property kind'] == 'loop invariant'])
            if success:
                return True, csv_output
            else:
                return False, csv_output

    def get_line_no_from_error_msg(self, checker_output):  
        pattern = r"on line (\d+): "
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
                if "loop invariant" in line:
                    invariants.append(line.strip())

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "while" in line:
                loc = index - 1
                break
        if loc is not None:
            lines = lines[: loc] + ["/*@\n"] + invariants + ["\n*/"] + lines[loc + 1 :]
        else:
            raise Exception("No while loop found")
        output = "\n".join(lines)

        return output

p = LoopyPipeline(benchmark=FramaCBenchmark(), checker=FramaCChecker()).load_config("config_frama_c.yaml")
p.run()

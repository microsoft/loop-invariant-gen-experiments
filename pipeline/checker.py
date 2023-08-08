import re
import subprocess


class Checker:
    def __init__(self, name="boogie"):
        self.name = name

    def check(self, code, mode, verbose=False):
        with open("/tmp/temp_eval.bpl", "w") as f:
            f.write(code)

        cmd = f"boogie /tmp/temp_eval.bpl /timeLimit:10"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        output = output.decode()

        if "1 verified" in output:
            return True, output
        else:
            return False, output

    def is_invariant(self, line):
        return "invariant" in line

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
            if self.is_invariant(lines[int(line_number)]):
                incorrect_invariants.append(lines[int(line_number)].strip())
        return "\n".join(incorrect_invariants)

    def prune_annotations_and_check(self, input_code):
        print("Pruning annotations")
        while True:
            status, error_string = self.check(input_code)
            invariant_line_mapping = {}
            lines = input_code.splitlines()
            for no, line in enumerate(lines):
                if self.is_invariant(line):
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

        return input_code

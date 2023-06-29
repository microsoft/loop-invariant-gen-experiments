import os
import subprocess
import re

NUM_COMPLETIONS = 3
BOOGIE_PARSED_DIR = "trusted_boogie_code"
BOOGIE_LLM_DIR = "boogie_code_gpt4"
BOOGIE_WITH_INV_INSERTED_DIR = "boogie_code_inv_inserted"
BOOGIE_ALL_INV = "boogie_code_all_inv_inserted"
BOOGIE_REMOVED_INV_SUCCESS = "boogie_code_pruned_success"
BOOGIE_REMOVED_INV_FAILURE = "boogie_code_pruned_failure"

def splice_invariants(boogie_code, invariants):
    lines = boogie_code.splitlines()
    loc = None
    for index, line in enumerate(lines):
        if "insert invariant" in line:
            loc = index
            break
    if loc is not None:
        lines = lines[:loc+1] + invariants + lines[loc+1:]
    else:
        raise Exception("No insert invariant found")

    output = '\n'.join(lines)
    return output

def get_invariants(boogie_code):
    invariants = []
    lines = boogie_code.splitlines()
    for line in lines:
        if "invariant" in line and "insert invariants" not in line:
            # line = line.replace("%", "mod")
            invariants.append(line.strip())
    return invariants

def insert_invariants(boogie_translated_code, boogie_inv_code):
    invariants = get_invariants(boogie_inv_code)
    return splice_invariants(boogie_translated_code, invariants)

def evaluate_boogie_file(file_name, print_output=False, print_command=False):
    # Run Boogie on the file and capture the output
    cmd = f'boogie {file_name} /timeLimit:10'
    p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
    output, err = p.communicate()
    output = output.decode()

    if print_command:
        print(cmd)

    if print_output:
        print(output)

    # Check if "1 verified" is in the output
    if "1 verified" in output:
        return True, output
    else:
        return False, output
    
def evaluate_boogie_code(boogie_code, print_output=False, print_command=False):
    with open("/tmp/temp_eval.bpl", "w") as f:
        f.write(boogie_code)
    return evaluate_boogie_file("/tmp/temp_eval.bpl", print_output, print_command)

def check_insert_invariant_keyword(boogie_code):
    for line in boogie_code.splitlines():
        if "insert invariant" in line:
            return True
    return False

def get_line_no_from_error_msg(error_string):
		# Define a regular expression to match the line numbers in the error message
		pattern = r"\((\d+),\d+\): Error"
		# Find all matches of the regular expression in the error message
		matches = re.findall(pattern, error_string)
		# Convert the matches to 0 indexed integers
		line_numbers = [int(match)-1 for match in matches]

		pattern = r"\((\d+),\d+\): error"
		matches = re.findall(pattern, error_string)
		line_numbers2 = [int(match)-1 for match in matches]

		# combine line_numbers and line_numbers2
		line_numbers = line_numbers + line_numbers2

		return line_numbers

def partition_invariants(boogie_code, print_progress=False):
    # parse error string to get line numbers
    # Then get invariants from boogie code according to line numbers. Ignore the postcondition. -> Create an invariant to line number mapping which you can index into
    while True:
        status, error_string = evaluate_boogie_code(boogie_code)
        if print_progress:
            for x in get_invariants(boogie_code):
                print(x)
            print("\n", error_string)
        invariant_line_mapping = {}
        lines = boogie_code.splitlines()
        for no, line in enumerate(lines):
            if "invariant" in line:
                invariant_line_mapping[no] = line

        (invariant_line_start, invariant_line_end) = list(invariant_line_mapping.keys())[0], list(invariant_line_mapping.keys())[-1]

        # get line numbers from error string
        line_numbers = get_line_no_from_error_msg(error_string)
        incorrect_invariant_line_numbers = [no for no in line_numbers if no in invariant_line_mapping.keys()]
        correct_invariant_line_numbers = [i for i in list(invariant_line_mapping.keys()) if i not in incorrect_invariant_line_numbers]

        if len(incorrect_invariant_line_numbers) == 0: break

        new_lines = lines[:invariant_line_start] + [lines[i] for i in correct_invariant_line_numbers] + lines[invariant_line_end+1:]
        new_file = "\n".join(new_lines)
        boogie_code = new_file
        status, _ = evaluate_boogie_code(boogie_code)
        if status:
            break

    return boogie_code

def evaluate_dir(dirname):
    success = 0
    failure = 0
    for index, file in enumerate(os.listdir(dirname)):
        status, output = evaluate_boogie_file(f"{dirname}/{file}")
        if not status:
            failure+=1
            print(f"{index} - {file}: Failure")
        else:
            success+=1
            print(f"{index} - {file}: Success")
    print("Success:", success)
    print("Failure:", failure)
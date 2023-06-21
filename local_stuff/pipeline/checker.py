import os
import subprocess
import re

NUM_COMPLETIONS = 3
BOOGIE_PARSED_DIR = "boogie_translated"
BOOGIE_LLM_DIR = "boogie_code_gpt4"
BOOGIE_WITH_INV_INSERTED_DIR = "boogie_code_inv_inserted"
BOOGIE_ALL_INV = "boogie_code_all_inv"
BOOGIE_REMOVED_INV_SUCCESS = "boogie_code_removed_inv_success"
BOOGIE_REMOVED_INV_FAILURE = "boogie_code_removed_inv_failure"

stats = {"Verified": 0, "Error": 0}
verified = []
error = []

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
    cmd = f'boogie {file_name}'
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

# def check_file(num):
#     file = f'{num}.bpl'
#     with open(f"{BOOGIE_PARSED_DIR}/{file}") as f:
#         boogie_translated_code = f.read()
#     for j in range(NUM_COMPLETIONS):
#         with open(f"{BOOGIE_LLM_DIR}/{file[:-4]}_{j}.bpl") as f:
#             boogie_llm_code = f.read()
#             boogie_with_inv_inserted_code = insert_invariants(boogie_translated_code, boogie_llm_code)
#             with open(f"{BOOGIE_WITH_INV_INSERTED_DIR}/{file[:-4]}_{j}.bpl", "w") as f2:
#                 f2.write(boogie_with_inv_inserted_code)
#                 res = evaluate_boogie_file(f"{file[:-4]}_{j}.bpl")
#                 if res:
#                     verified.append(f"{file[:-4]}_{j}.bpl")
#                     stats["Verified"] += 1
#                 else:
#                     error.append(f"{file[:-4]}_{j}.bpl")
#                     stats["Error"] += 1

def check_files():
    i = 0
    for trusted_boogie_root, dirs, files in os.walk(BOOGIE_PARSED_DIR):
        if 'code2inv' in trusted_boogie_root: continue
        for file in files:
            boogie_translated_code = open(os.path.join(trusted_boogie_root, file)).read()
            llm_boogie_root = trusted_boogie_root.replace(BOOGIE_PARSED_DIR, BOOGIE_LLM_DIR, 1)
            status = False

            if not check_insert_invariant_keyword(boogie_translated_code):
                print(f"Ignoring {file} since it does not have the insert invariant keyword")
                continue

            if os.path.exists(llm_boogie_root):
                for j in range(NUM_COMPLETIONS):
                    # if file == "73.bpl": breakpoint()
                    boogie_llm_code = open(os.path.join(llm_boogie_root, f"{file[:-4]}_{j}.bpl")).read()        
                    boogie_with_inv_inserted_code = insert_invariants(boogie_translated_code, boogie_llm_code)
                    output_root = trusted_boogie_root.replace(BOOGIE_PARSED_DIR, BOOGIE_WITH_INV_INSERTED_DIR, 1)
                    os.makedirs(output_root, exist_ok=True)
                    output_file_path = os.path.join(output_root, f"{file[:-4]}_{j}.bpl")
                    with open(output_file_path, "w") as f2:
                        f2.write(boogie_with_inv_inserted_code)
                    res, _ = evaluate_boogie_file(output_file_path, print_command=True)
                    status = res or status

                if status:
                    verified.append(file)
                    stats["Verified"] += 1
                else:
                    error.append(file)
                    stats["Error"] += 1
                i += 1
                print(i, file, status)

def combine_invariants():
    for trusted_boogie_root, dirs, files in os.walk(BOOGIE_PARSED_DIR):
        if 'code2inv' in trusted_boogie_root: continue
        for file in files:
            llm_boogie_root = trusted_boogie_root.replace(BOOGIE_PARSED_DIR, BOOGIE_LLM_DIR, 1)
            if os.path.exists(llm_boogie_root):
                boogie_translated_code = open(os.path.join(trusted_boogie_root, file)).read()
                
                if not check_insert_invariant_keyword(boogie_translated_code):
                    print(f"Ignoring {file} since it does not have the insert invariant keyword")
                    continue

                invariants = []
                for j in range(NUM_COMPLETIONS):
                        boogie_llm_code = open(os.path.join(llm_boogie_root, f"{file[:-4]}_{j}.bpl")).read()
                        invariants.extend(get_invariants(boogie_llm_code))

                output_root = trusted_boogie_root.replace(BOOGIE_PARSED_DIR, BOOGIE_ALL_INV, 1)
                os.makedirs(output_root, exist_ok=True)
                output_file_path = os.path.join(output_root, file)
                with open(output_file_path, "w") as f2:
                    f2.write(splice_invariants(boogie_translated_code, invariants))
                print(output_file_path)

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
        # breakpoint()

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
        

# Main Code

# # get stats for files in boogie_code_inv_inserted
# check_files()
# print(stats)

# # insert invariants from all llm files into parser translated code and write to boogie_code_all_inv
# combine_invariants()

# # evaluate boogie code with partitioned invariants
for root, dirs, files in os.walk(f"{BOOGIE_ALL_INV}/accelerating_invariant_generation"):
    for file in files:
        file_path = os.path.join(root, file)
        status, _ = evaluate_boogie_file(file_path)
        if not status:
            boogie_code_orig = open(file_path).read()
            boogie_code = boogie_code_orig
            boogie_code = partition_invariants(boogie_code)
            status, _ = evaluate_boogie_code(boogie_code)
            if status:
                output_root = root.replace(BOOGIE_ALL_INV, BOOGIE_REMOVED_INV_SUCCESS, 1)
                os.makedirs(output_root, exist_ok=True)
                with open(os.path.join(output_root, file), "w") as f2:
                    f2.write(boogie_code)
                print(f"Success {file} - Partitioned invariants")
                stats['Verified'] += 1
            else:
                output_root = root.replace(BOOGIE_ALL_INV, BOOGIE_REMOVED_INV_FAILURE, 1)
                os.makedirs(output_root, exist_ok=True)
                with open(os.path.join(output_root, file), "w") as f2:
                    f2.write(boogie_code_orig)
                print(f"Failed {file}")
                stats['Error'] += 1
        else:
            boogie_code = open(file_path).read()
            output_root = root.replace(BOOGIE_ALL_INV, BOOGIE_REMOVED_INV_SUCCESS, 1)
            os.makedirs(output_root, exist_ok=True)
            with open(os.path.join(output_root, file), "w") as f2:
                f2.write(boogie_code)
            print(f"Success {file} - No change")
            stats['Verified'] += 1
print(stats)

## OPTIONAL
# # evaluate diversity of invariants
# print("Number of completions for Invariant Generation:", NUM_COMPLETIONS)
# unique_invariants_len = []
# for i in range(1, 134):
#     with open(f"boogie_code_all_inv/{i}.bpl") as f:
#         boogie_code = f.read()
#         invariants = get_invariants(boogie_code)
#         invariants = list(set(invariants))
#         # print(f"{i}: {len(invariants)}")
#         unique_invariants_len.append(len(invariants))

# # Print bucketed values of unique_invariants_len
# buckets = {}
# for i in unique_invariants_len:
#     if i in buckets:
#         buckets[i] += 1
#     else:
#         buckets[i] = 1

# for i in sorted(buckets.keys()):
#     print(f"{i} Unique Invariants: {buckets[i]} files")

# # print average of numbers in unique_invariants_len
# print("Average # Unique Invariants:", sum(unique_invariants_len)/len(unique_invariants_len))

# evaluate_dir("final_boogie")
import os

def get_invariants(boogie_code):
    invariants = []
    lines = boogie_code.splitlines()
    for line in lines:
        if "invariant" in line and "insert invariants" not in line:
            # line = line.replace("%", "mod")
            invariants.append(line.strip())
    return invariants

DIR = "boogie_code_inv_inserted/code2inv"

unique_file_names_without_ext = set([x[:-6] for x in os.listdir(DIR)])

unique_inv_for_one_completion = {}
unique_inv_for_three_completion = {}
# 1 completion
for file in unique_file_names_without_ext:
    inv = get_invariants(open(os.path.join(DIR, f'{file}_0.bpl'), 'r').read())
    inv = list(set(inv))
    unique_inv_for_one_completion[file] = len(inv)

for file in unique_file_names_without_ext:
    inv_combined = []
    for j in range(0, 3):
        inv = get_invariants(open(os.path.join(DIR, f'{file}_{j}.bpl'), 'r').read())
        inv_combined.extend(list(set(inv)))
    inv_combined = list(set(inv_combined))
    unique_inv_for_three_completion[file] = len(inv_combined)

ratio_list = []
for file in unique_file_names_without_ext:
    ratio_list.append(unique_inv_for_three_completion[file] / unique_inv_for_one_completion[file])

print("Max:", max(ratio_list))
print("Min:", min(ratio_list))
print("Median:", sorted(ratio_list)[len(ratio_list) // 2])
print("Average:", sum(ratio_list) / len(ratio_list))


    
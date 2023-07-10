import pandas as pd
import numpy as np
import os, re


def strip_invariants_from_code(code):
		lines = code.splitlines()
		output_lines = []
		for index, line in enumerate(lines):
				if "invariant" in line:
					continue
				else:
					output_lines.append(line)
		return '\n'.join(output_lines)


def get_invariants(boogie_code):
    invariants = []
    lines = boogie_code.splitlines()
    for line in lines:
        if re.match(r"invariant .*;", line):
            line_ = line.strip()
            line_ = re.sub(r'//.*', '', line_)
            invariants.append(line_)
    return invariants


def set_primary_completions(df):
        for file_name in os.listdir(BOOGIE_WITH_INV_INSERTED_DIR):
                if file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_WITH_INV_INSERTED_DIR, file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[file_name.split('_')[0] + '.c', 'completion_' + str(int(file_name.split('_')[1].split('.')[0]) + 1)] = ' '.join([inv.replace('invariant ', '') for inv in invariants])


def set_primary_results(df):    
    for success_file_name in os.listdir(BOOGIE_PRUNED_INV_SUCCESS):
            if success_file_name.endswith(".bpl"):
                    with open(os.path.join(BOOGIE_PRUNED_INV_SUCCESS, success_file_name), 'r') as f:
                            boogie_code = f.read()
                            invariants = get_invariants(boogie_code)
                            df.loc[success_file_name.split('.')[0] + '.c', 'success_invs'] = ' '.join([inv.replace('invariant ', '') for inv in invariants])
    for failure_file_name in os.listdir(BOOGIE_PRUNED_INV_FAILURE):
                if failure_file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_PRUNED_INV_FAILURE, failure_file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[failure_file_name.split('.')[0] + '.c', 'failed_invs'] = ' '.join([inv.replace('invariant ', '') for inv in invariants]) 


def five_retries(df):
        for file_name in os.listdir(BOOGIE_HEALING_PRUNED_INV_SUCCESS):
                if file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_HEALING_PRUNED_INV_SUCCESS, file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[file_name.split('.')[0] + '.c', 'success_invs_healing_5'] = ' '.join([inv.replace('invariant ', '') for inv in invariants])

        for file_name in os.listdir(BOOGIE_HEALING_PRUNED_INV_FAILURE):
                if file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_HEALING_PRUNED_INV_FAILURE, file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[file_name.split('.')[0] + '.c', 'failed_invs_healing_5'] = ' '.join([inv.replace('invariant ', '') for inv in invariants])


def fifteen_retries(df):
        for file_name in os.listdir(BOOGIE_HEALING_FINAL_INV_SUCCESS):
                if file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_HEALING_FINAL_INV_SUCCESS, file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[file_name.split('.')[0] + '.c', 'success_invs_healing_15'] = ' '.join([inv.replace('invariant ', '') for inv in invariants])

        for file_name in os.listdir(BOOGIE_HEALING_FINAL_INV_FAILURE):
                if file_name.endswith(".bpl"):
                        with open(os.path.join(BOOGIE_HEALING_FINAL_INV_FAILURE, file_name), 'r') as f:
                                boogie_code = f.read()
                                invariants = get_invariants(boogie_code)
                                df.loc[file_name.split('.')[0] + '.c', 'failed_invs_healing_15'] = ' '.join([inv.replace('invariant ', '') for inv in invariants])


C_OLD_BENCHMARKS = "../pipeline/c_benchmarks/code2inv"
BOOGIE_PARSED_DIR = "../pipeline/trusted_boogie_code/code2inv"
BOOGIE_WITH_INV_INSERTED_DIR = "../pipeline/boogie_code_inv_inserted/code2inv"
BOOGIE_PRUNED_INV_SUCCESS = "../pipeline/boogie_code_pruned_success/code2inv"
BOOGIE_PRUNED_INV_FAILURE = "../pipeline/boogie_code_pruned_failure/code2inv"

BOOGIE_HEALING_PRUNED_INV_SUCCESS = "../healing/Archive/Retries_5/boogie_repaired_success" 
BOOGIE_HEALING_PRUNED_INV_FAILURE = "../healing/Archive/Retries_5/boogie_repaired_failed"

BOOGIE_HEALING_FINAL_INV_SUCCESS = "../healing/Archive/boogie_repaired_success" 
BOOGIE_HEALING_FINAL_INV_FAILURE = "../healing/Archive/boogie_repaired_failed"


df = pd.DataFrame(columns=['benchmark_name', 'completion_1', 'completion_2', 'completion_3', 'success_invs', 'failed_invs', \
                           'success_invs_healing_5', 'failed_invs_healing_5', 'success_invs_healing_15', 'failed_invs_healing_15'])
df['benchmark_name'] = os.listdir(C_OLD_BENCHMARKS)
df.set_index('benchmark_name', inplace=True)
df.sort_index(inplace=True, key=lambda x: x.str.split('.').str[0].astype(int))

set_primary_completions(df)
set_primary_results(df)
five_retries(df)
fifteen_retries(df)

buggy_benchmarks = ['106.c', '26.c', '27.c', '31.c', '32.c', '61.c', '62.c', '72.c', '75.c']
for i in buggy_benchmarks:
        df.loc[i, 'failed_invs_healing_15'] = "Buggy Benchmark. Skipped healing."
        df.loc[i, 'failed_invs_healing_5'] = "Buggy Benchmark. Skipped healing."
        df.loc[i, 'success_invs_healing_15'] = "Buggy Benchmark. Skipped healing."
        df.loc[i, 'success_invs_healing_5'] = "Buggy Benchmark. Skipped healing." 


for row in df.iterrows():
    if row[1]['success_invs'] == np.nan:
        assert(row[1]['failed_invs'] != np.nan)
    if row[1]['success_invs_healing_5'] == np.nan:
        assert(row[1]['failed_invs_healing_5'] != np.nan)
    if row[1]['success_invs_healing_15'] == np.nan:
        assert(row[1]['failed_invs_healing_15'] != np.nan)

    if row[1]['failed_invs'] == np.nan:
        assert(row[1]['success_invs'] != np.nan)
    if row[1]['failed_invs_healing_5'] == np.nan:
        assert(row[1]['success_invs_healing_5'] != np.nan)
    if row[1]['failed_invs_healing_15'] == np.nan:
        assert(row[1]['success_invs_healing_15'] != np.nan)

df.to_excel('code2inv_results.xlsx', engine='xlsxwriter')


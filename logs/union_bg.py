import json

with_nudges_log_file = open("loopy_2023_08_25_13_54_09_processed/final_output_combine_prune_re_filtered.json", "r", encoding="utf-8")
with_nudges_log = json.load(with_nudges_log_file)
with_nudges_log_file.close()

without_nudges_log_file = open("loopy_2023_08_25_13_52_59_processed/final_output_combine_re_filtered.json", "r", encoding="utf-8")
without_nudges_log = json.load(without_nudges_log_file)
without_nudges_log_file.close()

union_log = []
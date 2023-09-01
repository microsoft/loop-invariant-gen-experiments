import json

final_benchmarks__ = open("one_loop_one_method_no_arrays.txt").read().split("\n")

new_won_log = []

for k in range(1, 16):
    k_log = open(f"logs/loopy_2023_08_25_13_52_59_processed/pass_at_{k}_combine_and_prune.json")
    k_log = json.load(k_log)
    new_k_log = {"k": k, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []}
    assert k_log["k"] == k
    for i, b in enumerate(k_log["logs"]):
        if b["file"] in final_benchmarks__:
            new_k_log["logs"].append(b)
            new_k_log["pass_at_k"] += 0 if not "pass_at_k" in b.keys() else b["pass_at_k"]
            new_k_log["pass_at_k_prune"] += 0 if not "pass_at_k_prune" in b.keys() else b["pass_at_k_prune"]
    new_won_log.append(new_k_log)

with open(
    "logs/loopy_2023_08_25_13_52_59_processed/final_output_combine_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_won_log, f, indent=4, ensure_ascii=False)


new_wn_log = []

for k in range(1, 16):
    k_log = open(f"logs/loopy_2023_08_25_13_54_09_processed/pass_at_{k}_combine_and_prune.json")
    k_log = json.load(k_log)
    new_k_log = {"k": k, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []}
    assert k_log["k"] == k
    for i, b in enumerate(k_log["logs"]):
        if b["file"] in final_benchmarks__:
            new_k_log["logs"].append(b)
            new_k_log["pass_at_k"] += 0 if not "pass_at_k" in b.keys() else b["pass_at_k"]
            new_k_log["pass_at_k_prune"] += 0 if not "pass_at_k_prune" in b.keys() else b["pass_at_k_prune"]

    new_wn_log.append(new_k_log)

with open(
    "logs/loopy_2023_08_25_13_54_09_processed/final_output_combine_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_wn_log, f, indent=4, ensure_ascii=False)


new_m_log = []

for k in range(1, 16):
    k_log = open(f"logs/loopy_2023_08_27_02_50_01_processed/pass_at_{k}_combine_and_prune.json")
    k_log = json.load(k_log)
    new_k_log = {"k": k, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []}
    assert k_log["k"] == k
    for i, b in enumerate(k_log["logs"]):
        if b["file"] in final_benchmarks__:
            new_k_log["logs"].append(b)
            new_k_log["pass_at_k"] += 0 if not "pass_at_k" in b.keys() else b["pass_at_k"]
            new_k_log["pass_at_k_prune"] += 0 if not "pass_at_k_prune" in b.keys() else b["pass_at_k_prune"]

    new_m_log.append(new_k_log)

with open(
    "logs/loopy_2023_08_27_02_50_01_processed/final_output_combine_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_m_log, f, indent=4, ensure_ascii=False)


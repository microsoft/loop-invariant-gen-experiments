import json

final_benchmarks__ = open("one_loop_one_method_no_arrays.txt").read().split("\n")

won_p_processed = "logs/loopy_2023_08_25_13_52_59_processed/final_output_no_prune.json"
wn_p_processed = "logs/loopy_2023_08_25_13_54_09_processed/final_output_no_prune.json"
m_p_processed = "logs/loopy_2023_08_27_02_50_01_processed/final_output_no_prune.json"

wonp_processed = json.load(open(won_p_processed, encoding="utf-8"))
wnp_processed = json.load(open(wn_p_processed, encoding="utf-8"))
mp_processed = json.load(open(m_p_processed, encoding="utf-8"))

new_logs_1 = [
    {"k": i, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []} for i in range(1, 16)
]
for k in range(1, 16):
    assert wonp_processed[k - 1]["k"] == k
    new_log = new_logs_1[k - 1]["logs"]
    pass_at_k = 0.0
    for i, b in enumerate(wonp_processed[k - 1]["logs"]):
        if b["file"] in final_benchmarks__:
            new_logs_1[k - 1]["logs"].append(b)
            new_logs_1[k - 1]["pass_at_k"] += b["pass_at_k"]

with open(
    "logs/loopy_2023_08_25_13_52_59_processed/final_output_no_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_logs_1, f, indent=4, ensure_ascii=False)

new_logs_1 = [
    {"k": i, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []} for i in range(1, 16)
]
for k in range(1, 16):
    assert wnp_processed[k - 1]["k"] == k
    new_log = new_logs_1[k - 1]["logs"]
    pass_at_k = 0.0
    for i, b in enumerate(wnp_processed[k - 1]["logs"]):
        if b["file"] in final_benchmarks__:
            new_logs_1[k - 1]["logs"].append(b)
            new_logs_1[k - 1]["pass_at_k"] += b["pass_at_k"]

with open(
    "logs/loopy_2023_08_25_13_54_09_processed/final_output_no_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_logs_1, f, indent=4, ensure_ascii=False)

new_logs_1 = [
    {"k": i, "pass_at_k": 0.0, "pass_at_k_prune": 0.0, "logs": []} for i in range(1, 16)
]
for k in range(1, 16):
    assert mp_processed[k - 1]["k"] == k
    new_log = new_logs_1[k - 1]["logs"]
    pass_at_k = 0.0
    for i, b in enumerate(mp_processed[k - 1]["logs"]):
        if b["file"] in final_benchmarks__:
            new_logs_1[k - 1]["logs"].append(b)
            new_logs_1[k - 1]["pass_at_k"] += b["pass_at_k"]

with open(
    "logs/loopy_2023_08_27_02_50_01_processed/final_output_no_prune_re_filtered.json",
    "w",
    encoding="utf-8",
) as f:
    json.dump(new_logs_1, f, indent=4, ensure_ascii=False)
    
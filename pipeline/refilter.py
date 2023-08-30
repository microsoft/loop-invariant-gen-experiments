import json

final_benchmarks__ = open("one_loop_one_method_no_arrays.txt").read().split('\n')

m_p_lf_1 = "logs/loopy_2023_08_27_02_50_01/final_rechecked.json"
m_p_lf_2 = "logs/loopy_2023_08_17_03_55_30/final_rechecked.json"

wn_p_lf_1 = "logs/loopy_2023_08_25_13_54_09/final_rechecked.json"
wn_p_lf_2 = "logs/loopy_2023_08_13_23_52_42/final_rechecked_rechecked.json"

won_p_lf_1 = "logs/loopy_2023_08_25_13_52_59/final_rechecked.json"
won_p_lf_2 = "logs/loopy_2023_08_13_23_52_36/final_rechecked_rechecked.json"

mp_lf1 = json.load(open(m_p_lf_1, encoding="utf-8"))
mp_lf2 = json.load(open(m_p_lf_2, encoding="utf-8"))

wnp_lf1 = json.load(open(wn_p_lf_1, encoding="utf-8"))
wnp_lf2 = json.load(open(wn_p_lf_2, encoding="utf-8"))

wonp_lf1 = json.load(open(won_p_lf_1, encoding="utf-8"))
wonp_lf2 = json.load(open(won_p_lf_2, encoding="utf-8"))

new_log_1 = []
new_log_2 = []
log3 = {"check": [], "prune": []}
for i, b in enumerate(mp_lf1["logs"]):
    assert b["file"] == mp_lf2["logs"][i]["file"]
    if b["file"] in final_benchmarks__:
        new_log_1.append(b)
        new_log_2.append(mp_lf2["logs"][i])
    else:
        if "checker_output" in b.keys() and b["checker_output"]:
            log3["check"].append(b)
        if "checker_output_after_combine_and_prune" in b.keys() and b["checker_output_after_combine_and_prune"]:
            log3["prune"].append(b)

mp_lf1["logs"] = new_log_1
mp_lf2["logs"] = new_log_2
json.dump(mp_lf1, open(m_p_lf_1.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)
json.dump(mp_lf2, open(m_p_lf_2.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)

new_log_3 = []
new_log_4 = []
log4 = {"check": [], "prune": []}
for i, b in enumerate(wnp_lf1["logs"]):
    assert b["file"] == wnp_lf2["logs"][i]["file"]
    if b["file"] in final_benchmarks__:
        new_log_3.append(b)
        new_log_4.append(wnp_lf2["logs"][i])
    else:
        if "checker_output" in b.keys() and b["checker_output"]:
            log4["check"].append(b)
        if "checker_output_after_combine_and_prune" in b.keys() and b["checker_output_after_combine_and_prune"]:
            log4["prune"].append(b)

wnp_lf1["logs"] = new_log_3
wnp_lf2["logs"] = new_log_4

json.dump(wnp_lf1, open(wn_p_lf_1.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)
json.dump(wnp_lf2, open(wn_p_lf_2.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)

new_log_5 = []
new_log_6 = []
log5 = {"check": [], "prune": []}
for i, b in enumerate(wonp_lf1["logs"]):
    assert b["file"] == wonp_lf2["logs"][i]["file"]
    if b["file"] in final_benchmarks__:
        new_log_5.append(b)
        new_log_6.append(wonp_lf2["logs"][i])
    else:
        if "checker_output" in b.keys() and b["checker_output"]:
            log5["check"].append(b)
        if "checker_output_after_combine_and_prune" in b.keys() and b["checker_output_after_combine_and_prune"]:
            log5["prune"].append(b)

wonp_lf1["logs"] = new_log_5
wonp_lf2["logs"] = new_log_6

json.dump(wonp_lf1, open(won_p_lf_1.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)
json.dump(wonp_lf2, open(won_p_lf_2.replace(".json", "_re_filtered.json"), "w", encoding='utf-8'), indent=4, ensure_ascii=False)

json.dump(log3, open("logs/minimal_prompt_array.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
json.dump(log4, open("logs/with_nudges_array.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)
json.dump(log5, open("logs/without_nudges_array.json", "w", encoding="utf-8"), indent=4, ensure_ascii=False)

won_p_processed = "logs/loopy_2023_08_25_13_52_59_processed/final_output_no_prune.json"
wn_p_processed = "logs/loopy_2023_08_25_13_54_09_processed/final_output_no_prune.json"
m_p_processed = "logs/loopy_2023_08_27_02_50_01_processed/final_output_no_prune.json"

wonp_processed = json.load(open(won_p_processed, encoding="utf-8"))
wnp_processed = json.load(open(wn_p_processed, encoding="utf-8"))
mp_processed = json.load(open(m_p_processed, encoding="utf-8"))

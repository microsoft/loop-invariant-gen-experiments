import json

old_logs_file = open("final_merged_rechecked_logs.json", "r", encoding='utf-8')
old_logs = json.load(old_logs_file)
old_logs_file.close()
old_logs = old_logs["logs"]

new_logs_file = open("loopy_2023_08_09_03_53_03/final.json", "r", encoding='utf-8')
new_logs = json.load(new_logs_file)
new_logs_file.close()
new_logs = new_logs["logs"]

benchmark_files_file = open("../oneloop_onemethod_1.txt", "r", encoding='utf-8')
benchmark_files = benchmark_files_file.readlines()
benchmark_files_file.close()
benchmark_files = [x.strip() for x in benchmark_files]

latest_logs = {}
latest_logs["logs"] = []
for log in old_logs:
    if log["file"] in benchmark_files:
        latest_logs["logs"].append(log)
for log in new_logs:
    if log["file"] in benchmark_files and log["file"] not in [x["file"] for x in old_logs]:
        latest_logs["logs"].append(log)
latest_logs["stats"] = {}
latest_logs["stats"]["success"] = []
latest_logs["stats"]["failure"] = []
latest_logs["stats"]["need_nudging"] = []
latest_logs["stats"]["skipped"] = []
latest_logs["stats"]["success_without_nudging"] = []
latest_logs["stats"]["success_with_nudging"] = []
latest_logs["stats"]["success_without_nudging_with_prune"] = []
latest_logs["stats"]["success_with_nudging_with_prune"] = []
latest_logs["stats"]["success_count"] = 0
latest_logs["stats"]["failure_count"] = 0
latest_logs["stats"]["need_nudging_count"] = 0
latest_logs["stats"]["skipped_count"] = 0
latest_logs["stats"]["success_without_nudging_count"] = 0
latest_logs["stats"]["success_with_nudging_count"] = 0
latest_logs["stats"]["total"] = 0
latest_logs["stats"]["success_rate"] = 0
for x, i in enumerate(latest_logs["logs"]):
    if "error" in i.keys():
        latest_logs["stats"]["skipped"].append(x)
    elif i["checker_output"] or i["checker_output_after_prune"]:
        latest_logs["stats"]["success"].append(x)
        if i["checker_output"]:
            latest_logs["stats"]["success_without_nudging"].append(x)
        elif "checker_output_after_prune" in i.keys() and i["checker_output_after_prune"]:
            latest_logs["stats"]["success_without_nudging_with_prune"].append(x)
    elif "checker_output_after_nudge" not in i.keys():
        latest_logs["stats"]["need_nudging"].append(x)
    elif i["checker_output_after_nudge"] or i["checker_output_after_nudge_and_prune"]:
        latest_logs["stats"]["success"].append(x)
        if i["checker_output_after_nudge"]:
            latest_logs["stats"]["success_with_nudging"].append(x)
        elif "checker_output_after_nudge_and_prune" in i.keys() and i["checker_output_after_nudge_and_prune"]:
            latest_logs["stats"]["success_with_nudging_with_prune"].append(x)
    else:
        latest_logs["stats"]["failure"].append(x)
latest_logs["stats"]["success_count"] = len(latest_logs["stats"]["success"])
latest_logs["stats"]["failure_count"] = len(latest_logs["stats"]["failure"])
latest_logs["stats"]["success_without_nudging_count"] = len(latest_logs["stats"]["success_without_nudging"])
latest_logs["stats"]["success_without_nudging_with_prune"] = len(latest_logs["stats"]["success_without_nudging_with_prune"])
latest_logs["stats"]["success_with_nudging_count"] = len(latest_logs["stats"]["success_with_nudging"])
latest_logs["stats"]["success_with_nudging_with_prune"] = len(latest_logs["stats"]["success_with_nudging_with_prune"])
latest_logs["stats"]["skipped_count"] = len(latest_logs["stats"]["skipped"])
latest_logs["stats"]["need_nudging_count"] = len(latest_logs["stats"]["need_nudging"])
latest_logs["stats"]["total"] = len(latest_logs["logs"])
latest_logs["stats"]["success_rate"] = latest_logs["stats"]["success_count"] / (latest_logs["stats"]["success_count"] + latest_logs["stats"]["failure_count"])
with open("with_nudging_merged_restat.json", "w", encoding='utf-8') as f:
    json.dump(latest_logs, f, indent=4, ensure_ascii=False)


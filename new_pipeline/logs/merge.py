import json


with open("loopy_2023_08_03_20_54_22/final.json", "r", encoding="utf-8") as f:
    data = json.load(f)
    logs = data["logs"]
    new_logs = []
    for x, i in enumerate(logs):
        if "inter_procedural" in i.keys() or "multi_loop" in i.keys():
            if x in data["stats"]["failure"]:
                data["stats"]["failure"].remove(x)
            continue
        else:
            new_logs.append(i)
    data["logs"] = new_logs
    data["stats"]["total"] = len(new_logs)
    data["stats"]["success_count"] = len(data["stats"]["success"])
    data["stats"]["failure_count"] = len(data["stats"]["failure"])
    data["stats"]["success_rate"] = data["stats"]["success_count"] / data["stats"]["total"]

    with open(
        "loopy_2023_08_03_20_54_22/final_merged.json", "w", encoding="utf-8"
    ) as f:
        json.dump(data, f, indent=4, ensure_ascii=False)


# with open("final_rechecked_logs.json", "r", encoding='utf-8') as f:
#     data = json.load(f)
#     logs  = data["logs"]
#     stats = {"success": [], "failure": [], "need_nudging": [], "success_count": 0, "failure_count": 0, "total": 0, "success_rate": 0}
#     stats["need_nudging"] = []
#     for x, i in enumerate(logs):
#         if "error" in i.keys():
#             stats["failure"].append(x)
#         elif i["checker_output"] or i["checker_output_after_prune"]:
#             stats["success"].append(x)
#         elif "checker_output_after_nudge" not in i.keys():
#             stats["need_nudging"].append(x)
#         elif i["checker_output_after_nudge"] or i["checker_output_after_nudge_and_prune"]:
#             stats["success"].append(x)
#         else:
#             stats["failure"].append(x)
#     stats["success_count"] = len(stats["success"])
#     stats["failure_count"] = len(stats["failure"])
#     stats["need_nudging_count"] = len(stats["need_nudging"])
#     stats["total"] = len(logs)
#     stats["success_rate"] = len(stats["success"]) / len(logs)
#     data["stats"] = stats
#     with open("final_merged_rechecked_logs.json", "w", encoding='utf-8') as f:
#         json.dump(data, f, indent=4, ensure_ascii=False)

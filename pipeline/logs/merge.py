import json


with open("loopy_2023_08_03_20_54_22/final.json", "r", encoding="utf-8") as f:
    with open("loopy_2023_08_07_03_49_07/final.json", "r", encoding="utf-8") as f2:
        data = json.load(f)
        data2 = json.load(f2)
        logs = data["logs"]
        logs2 = data2["logs"]
        new_logs = []
        for x, i in enumerate(logs2):
            if "inter_procedural" in logs[x].keys() or "multi_loop" in logs[x].keys():
                if x in data2["stats"]["failure"]:
                    data2["stats"]["failure"].remove(x)
                continue
            else:
                new_logs.append(i)
        data2["logs"] = new_logs
        data2["stats"]["total"] = len(new_logs)
        data2["stats"]["success_count"] = len(data2["stats"]["success"])
        data2["stats"]["failure_count"] = len(data2["stats"]["failure"])
        data2["stats"]["success_rate"] = data2["stats"]["success_count"] / data2["stats"]["total"]

        with open(
            "loopy_2023_08_07_03_49_07/final_merged.json", "w", encoding="utf-8"
        ) as f3:
            json.dump(data2, f3, indent=4, ensure_ascii=False)


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

import json

with open("without_nudge_merged.json", "r", encoding='utf-8') as f:
    data = json.load(f)
    logs  = data["logs"]
    stats = {"success": [], "failure": [], "success_count": 0, "failure_count": 0, "total": 0, "success_rate": 0}
    for x, i in enumerate(logs):
        if "error" in i.keys():
            stats["failure"].append(x)
        elif i["checker_output"] or i["checker_output_after_prune"]:
            stats["success"].append(x)
        else:
            stats["failure"].append(x)
    stats["success_count"] = len(stats["success"])
    stats["failure_count"] = len(stats["failure"])
    stats["total"] = len(logs)
    stats["success_rate"] = len(stats["success"]) / len(logs)
    data["stats"] = stats
    with open("without_nudge_merged_restat.json", "w", encoding='utf-8') as f:
        json.dump(data, f, indent=4, ensure_ascii=False)
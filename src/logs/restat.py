import json

with open("without_nudge_merged.json", "r", encoding="utf-8") as f:
    data = json.load(f)
    logs = data["logs"]
    stats = {
        "success": [],
        "failure": [],
        "skipped": [],
        "success_without_prune": [],
        "success_with_prune": [],
        "success_count": 0,
        "failure_count": 0,
        "total": 0,
        "success_rate": 0,
        "success_without_prune_count": 0,
        "success_with_prune_count": 0,
    }
    for x, i in enumerate(logs):
        if "error" in i.keys():
            stats["skipped"].append(x)
        elif i["checker_output"] or i["checker_output_after_prune"]:
            stats["success"].append(x)
            if i["checker_output"]:
                stats["success_without_prune"].append(x)
            elif "checker_output_after_prune" in i.keys() and i["checker_output_after_prune"]:
                stats["success_with_prune"].append(x)
        else:
            stats["failure"].append(x)
    stats["success_count"] = len(stats["success"])
    stats["failure_count"] = len(stats["failure"])
    stats["skipped_count"] = len(stats["skipped"])
    stats["success_without_prune_count"] = len(stats["success_without_prune"])
    stats["success_with_prune_count"] = len(stats["success_with_prune"])
    stats["total"] = len(logs)
    stats["success_rate"] = stats["success_count"] / (
        stats["success_count"] + stats["failure_count"]
    )
    data["stats"] = stats
    with open("without_nudge_merged_restat.json", "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)

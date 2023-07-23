# import json

# with open("logs/loopy_2023_07_21_11_45_12.json", "r", encoding='utf-8') as f:
#     data = json.load(f)

# # fixing_need = []

# # for x, i in enumerate(data["logs"]):
# #     if "error" in i.keys():
# #         if i["error"] == "Output does not contain 1 code block":
# #             fixing_need.append(x)

# # print(" ".join([str(x) for x in fixing_need]))

# success = []
# failure = []

# for x, i in enumerate(data["logs"]):
#     i["file"] = "pipeline/c_benchmarks/code2inv/" + str(x + 1) + ".c"
#     if i["checker_output"] or i["checker_output_after_prune"]:
#         success.append(x)
#     else:
#         failure.append(x)
# data["stats"] = {
#     "success": success,
#     "success_count": len(success),
#     "failure": failure,
#     "failure_count": len(failure),
#     "total": len(data["logs"]),
#     "success_rate": len(success) / len(data["logs"])
# }

# with open("logs/loopy_2023_07_21_11_45_12.json", "w", encoding='utf-8') as f:
#     json.dump(data, f, indent=4, ensure_ascii=False)


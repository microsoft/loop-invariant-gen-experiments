import json

with open("logs/loopy_2023_07_21_11_45_12.json", "r", encoding='utf-8') as f:
    data = json.load(f)

fixing_need = []

for x, i in enumerate(data["logs"]):
    if "error" in i.keys():
        if i["error"] == "Output does not contain 1 code block":
            fixing_need.append(x)

print(" ".join([str(x) for x in fixing_need]))
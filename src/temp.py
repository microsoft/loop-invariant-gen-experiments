import json
import os
import traceback

from frama_c import FramaCBenchmark, InvalidBenchmarkException

files_initial = open(
    "../dataset_analysis/svcomp_reachsafety_files.txt", "r"
).read().split("\n")

fb = FramaCBenchmark(features="multiple_loops_multiple_methods")
valid_files = []
invalid_files = []

for file in files_initial:
    try:
        if not os.path.exists(file):
            print("File not found: " + file)
            file = file[:-2] + ".i"
            if not os.path.exists(file):
                print("File not found: " + file)
                continue
        code = open(file.strip(), "r").read()
        fb.preprocess(code, "multiple_loops_multiple_methods")
        valid_files.append(file.strip())
        print("Valid: " + file.strip())
    except InvalidBenchmarkException as e:
        print()
        invalid_files.append(file.strip())
        print(f"[{str(e)}] Invalid: {file.strip()}")

with open("../experiments/svcomp_reachsafety_filtered.txt", "w") as f:
    f.write("\n".join(valid_files))

with open("invalid_files.txt", "w") as f:
    f.write("\n".join(invalid_files))

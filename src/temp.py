import json
import os
import traceback
import pandas as pd

from frama_c import FramaCBenchmark, InvalidBenchmarkException

files_initial = open("../dataset_analysis/svcomp_files.txt", "r").read().split("\n")

fb = FramaCBenchmark(features="multiple_loops_multiple_methods")
file_features = []

for file in files_initial:
    try:
        if not os.path.exists(file):
            print("File not found: " + file)
            file = file[:-2] + ".i"
            if not os.path.exists(file):
                print("File not found: " + file)
                continue
        code = open(file.strip(), "r").read()
        (
            num_loops,
            more_than_one_method,
            uses_arrays,
            uses_pointers,
            num_lines,
        ) = fb.preprocess(code, "multiple_loops_multiple_methods")
        file_features.append(
            {
                "file": file.strip(),
                "num_loops": num_loops,
                "more_than_one_method": more_than_one_method,
                "uses_arrays": uses_arrays,
                "uses_pointers": uses_pointers,
                "num_lines": num_lines,
            }
        )

    except InvalidBenchmarkException as e:
        file_features.append(
            {
                "file": file.strip(),
                "num_loops": None,
                "more_than_one_method": None,
                "uses_arrays": None,
                "uses_pointers": None,
                "num_lines": None,
                "error": str(e),
            }
        )
        print(f"[{str(e)}] Invalid: {file.strip()}")

with open("svcomp_features.json", "w") as f:
    json.dump(file_features, f, indent=4)

import json
import os
import traceback
from llm_utils import Logger

from frama_c import FramaCBenchmark, InvalidBenchmarkException

files_initial = open("../experiments/all_benchmarks.txt", "r").read().split("\n")

fb = FramaCBenchmark(features="one_loop_one_method")
file_features = []

for index, file in enumerate(files_initial):
    try:
        Logger.log_info(f"Processing {index + 1}/{len(files_initial)}: {file}")
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
        ) = fb.preprocess(code, "one_loop_one_method")
        Logger.log_info(
            f"Num loops: {num_loops}, more than one method: {more_than_one_method}, uses arrays: {uses_arrays}, uses pointers: {uses_pointers}, num lines: {num_lines}"
        )
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

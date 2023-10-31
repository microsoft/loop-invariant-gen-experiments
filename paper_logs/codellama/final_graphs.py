import json
import multiprocessing

import sys
import traceback

sys.path.append("../../src/")

from frama_c import FramaCBenchmark, FramaCChecker
from llm_utils import Logger
from process_results import prune_wrapper

success_without_houdini = []
success_with_houdini = []
to_rerun = []

failure_candidates = []
culprits = {}

code2inv_stats = {"without_houdini": {}, "with_houdini": {}}
code2inv_file = json.load(open("code2inv/loopy_2023_10_22_01_14_08/final.json", "r"))

for code2inv in code2inv_file["logs"]:
    success = False
    sprune = False
    if "completions" not in code2inv:
        to_rerun.append(code2inv["file"])
        continue
    any_success = False
    for completion in code2inv["completions"]:
        if "success" in completion:
            any_success = any_success or completion["success"]
        elif "checker_output_for_annotations" in completion:
            any_success = any_success or completion["checker_output_for_annotations"]

        if "checker_output_after_prune" in completion:
            if completion["checker_output_after_prune"]:
                code2inv_stats["with_houdini"][code2inv["file"]] = True
                sprune = True

    if any_success:
        success = True
        code2inv_stats["without_houdini"][(code2inv["file"])] = True
    else:
        if "checker_output_after_prune" in code2inv:
            if code2inv["checker_output_after_prune"]:
                success = True
                code2inv_stats["with_houdini"][(code2inv["file"])] = True
            elif sprune:
                culprits[code2inv["file"]] = True
                continue
        elif "checker_output" in code2inv:
            if code2inv["checker_output"]:
                success = True
                code2inv_stats["with_houdini"][(code2inv["file"])] = True
        else:
            to_rerun.append(code2inv["file"])
    if not success:
        failure_candidates.append(
            (code2inv["file"], code2inv["code_with_combined_annotations"])
        )

print("====================== Code2Inv benchmarks ======================")
print("To rerun: ", len(to_rerun))
print("Without houdini: ", len(code2inv_stats["without_houdini"]))
print("With houdini: ", len(code2inv_stats["with_houdini"]))
print("=================================================================")


old_benchmarks_stats = {"without_houdini": {}, "with_houdini": {}}
old_benchmarks = json.load(open("old_mix/loopy_2023_09_25_08_57_18/final.json", "r"))

for benchmark in old_benchmarks["logs"]:
    success = False
    sprune = False
    if "completions" not in benchmark:
        to_rerun.append(benchmark["file"])
        continue
    any_success = False
    for completion in benchmark["completions"]:
        if "success" in completion:
            any_success = any_success or completion["success"]
        
        if "success_after_prune" in completion:
            if completion["success_after_prune"]:
                old_benchmarks_stats["with_houdini"][benchmark["file"]] = True
                sprune = True

    if any_success:
        success = True
        old_benchmarks_stats["without_houdini"][(benchmark["file"])] = True
    else:
        if "checker_output_after_combine_and_prune" in benchmark:
            if benchmark["checker_output_after_combine_and_prune"]:
                success = True
                old_benchmarks_stats["with_houdini"][(benchmark["file"])] = True
            elif sprune:
                culprits[benchmark["file"]] = True
                continue
        elif "checker_output" in benchmark:
            if benchmark["checker_output"]:
                success = True
                old_benchmarks_stats["with_houdini"][(benchmark["file"])] = True
        else:
            print("No prune output for ", benchmark["file"])
            to_rerun.append(benchmark["file"])
    if not success:
        failure_candidates.append(
            (benchmark["file"], benchmark["code_with_combined_invariants"])
        )

print("====================== Old benchmarks ======================")
print("To rerun: ", len(to_rerun))
print("Without houdini: ", len(old_benchmarks_stats["without_houdini"]))
print("With houdini: ", len(old_benchmarks_stats["with_houdini"]))
print("============================================================")


diff_files_stats = {"without_houdini": {}, "with_houdini": {}}
diff_files = json.load(open("diff_files/loopy_2023_10_30_17_04_27/final.json", "r"))

for diff_file in diff_files["logs"]:
    success = False
    sprune = False
    if "completions" not in diff_file:
        to_rerun.append(diff_file["file"])
        continue
    any_success = False
    for completion in diff_file["completions"]:
        if "success" in completion:
            any_success = any_success or completion["success"]
        elif "checker_output_for_annotations" in completion:
            any_success = any_success or completion["checker_output_for_annotations"]
        
        if "checker_output_after_prune" in completion:
            if completion["checker_output_after_prune"]:
                diff_files_stats["with_houdini"][diff_file["file"]] = True
                sprune = True

    if any_success:
        success = True
        diff_files_stats["without_houdini"][(diff_file["file"])] = True
    else:
        if "checker_output_after_prune" in diff_file:
            if diff_file["checker_output_after_prune"]:
                success = True
                diff_files_stats["with_houdini"][(diff_file["file"])] = True
            elif sprune:
                culprits[diff_file["file"]] = True
                continue
        elif "checker_output_after_combine_and_prune" in diff_file:
            if diff_file["checker_output_after_combine_and_prune"]:
                success = True
                diff_files_stats["with_houdini"][(diff_file["file"])] = True
        elif "checker_output_for_combined_annotations" in diff_file:
            if diff_file["checker_output"]:
                success = True
                diff_files_stats["with_houdini"][(diff_file["file"])] = True
        else:
            to_rerun.append(diff_file["file"])
    if not success:
        failure_candidates.append(
            (diff_file["file"], diff_file["code_with_combined_annotations"])
        )

print("====================== Diff files ======================")
print("To rerun: ", len(to_rerun))
print("Without houdini: ", len(diff_files_stats["without_houdini"]))
print("With houdini: ", len(diff_files_stats["with_houdini"]))
print("========================================================")

print("Total numbers: ")
print(
    "Without houdini: ",
    len(code2inv_stats["without_houdini"])
    + len(old_benchmarks_stats["without_houdini"])
    + len(diff_files_stats["without_houdini"]),
)
print(
    "With houdini: ",
    len(code2inv_stats["with_houdini"])
    + len(old_benchmarks_stats["with_houdini"])
    + len(diff_files_stats["with_houdini"])
    + len(code2inv_stats["without_houdini"])
    + len(old_benchmarks_stats["without_houdini"])
    + len(diff_files_stats["without_houdini"]),
)
print("Failure candidates: ", len(failure_candidates))
print("Culprits: ", len(culprits))

# with open("files_to_rerun.txt", "w") as f:
#     for file in to_rerun:
#         f.write(file + "\n")

# with open("culprit_files.txt", "w") as f:
#     for file in culprits:
#         f.write(file + "\n")

# def run_parallel(inputs, func):
#     assert len(inputs) <= 32

#     pool = multiprocessing.Pool(processes=len(inputs))
#     results = pool.map(func, inputs)
#     pool.close()
#     pool.join()
#     return results


# def prune_wrapper(checker_input):
#     checker = FramaCChecker()
#     success = False
#     pruned_code = None
#     try:
#         success, pruned_code, _ = checker.houdini(
#             checker_input,
#             features="one_loop_one_method",
#             use_json_dump_for_invariants=True,
#         )
#     except Exception as e:
#         print(e)
#         traceback.print_exc()
#     return success, pruned_code


# rechecking_json = {"logs": []}
# checker = FramaCChecker()

# max_iters = len(failure_candidates) // 32 + 1

# for i in range(0, max_iters):
#     Logger.log_info(f"Rechecking {i+1}/{len(failure_candidates)}")
#     benchmarks = failure_candidates[i : i + 32]
#     benchmarks = [x[1] for x in benchmarks]
#     results = run_parallel(benchmarks, prune_wrapper)
#     for benchmark, result in zip(benchmarks, results):
#         benchmark_json = {"file": benchmark[0], "code": benchmark[1]}
#         benchmark_json["checker_output"] = result[0]
#         benchmark_json["code_with_pruned_annotations"] = result[1]
#         rechecking_json["logs"].append(benchmark_json)
#         if result[0]:
#             Logger.log_success(f"Rechecking {i+1}/{len(failure_candidates)}: Success")
#         else:
#             Logger.log_error(f"Rechecking {i+1}/{len(failure_candidates)}: Failure")

# with open("rechecking.json", "w") as f:
#     json.dump(rechecking_json, f, indent=4)

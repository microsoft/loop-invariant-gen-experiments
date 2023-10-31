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
to_rerun = {}

failure_candidates = []

code2inv_stats = {"without_houdini": [], "with_houdini": []}
code2inv_file = json.load(
    open("with_nudges/code2inv/loopy_2023_10_03_02_16_01/final_rechecked.json", "r")
)

for code2inv in code2inv_file["logs"]:
    success = False
    if "completions" not in code2inv:
        to_rerun[code2inv["file"]] = True
        continue
    any_success = False
    for completion in code2inv["completions"]:
        if "success" in completion:
            any_success = any_success or completion["success"]
        elif "checker_output_for_annotations" in completion:
            any_success = any_success or completion["checker_output_for_annotations"]

    if any_success:
        success = True
        code2inv_stats["without_houdini"].append(code2inv["file"])
    else:
        if "checker_output_after_prune" in code2inv:
            if code2inv["checker_output_after_prune"]:
                success = True
                code2inv_stats["with_houdini"].append(code2inv["file"])
        elif "checker_output_after_combine_and_prune" in code2inv:
            if code2inv["checker_output_after_combine_and_prune"]:
                success = True
                code2inv_stats["with_houdini"].append(code2inv["file"])
        elif "checker_output" in code2inv:
            if code2inv["checker_output"]:
                success = True
                code2inv_stats["with_houdini"].append(code2inv["file"])
        else:
            to_rerun[(code2inv["file"])] = True
    if not success:
        failure_candidates.append(
            (code2inv["file"], code2inv["code_with_combined_invariants"])
        )


def run_parallel(inputs, func):
    assert len(inputs) <= 32

    pool = multiprocessing.Pool(processes=len(inputs))
    results = pool.map(func, inputs)
    pool.close()
    pool.join()
    return results


def prune_wrapper(checker_input):
    checker = FramaCChecker()
    success = False
    pruned_code = None
    try:
        success, pruned_code, _ = checker.houdini(
            checker_input,
            features="one_loop_one_method",
            use_json_dump_for_invariants=True,
        )
    except Exception as e:
        print(e)
        traceback.print_exc()
    return success, pruned_code


rechecking_json = {"logs": []}
checker = FramaCChecker()
framac_benchmark = FramaCBenchmark(features="one_loop_one_method")

max_iters = (len(failure_candidates) // 32) + 1

for i in range(0, max_iters):
    Logger.log_info(f"Rechecking {i+1}/{max_iters}")
    benchmarks = failure_candidates[i : i + 32]
    benchmarks_with_files = benchmarks
    benchmarks = [x[1] for x in benchmarks]
    results = run_parallel(benchmarks, prune_wrapper)
    for benchmark, result in zip(benchmarks_with_files, results):
        benchmark_json = {"file": benchmark[0], "code": benchmark[1]}
        benchmark_json["checker_output"] = result[0]
        benchmark_json["code_with_pruned_annotations"] = result[1]
        rechecking_json["logs"].append(benchmark_json)
        if result[0]:
            Logger.log_success(f"Rechecking {benchmark[0]}: Success")
        else:
            Logger.log_error(f"Rechecking {benchmark[0]}: Failure")

with open("rechecking1.json", "w") as f:
    json.dump(rechecking_json, f, indent=4)

# indices = [
#     int(file.split("/")[-1].split(".")[0]) - 1
#     for file in code2inv_stats["with_houdini"]
# ]
# indices += [
#     int(file.split("/")[-1].split(".")[0]) - 1
#     for file in code2inv_stats["without_houdini"]
# ]
# indices = sorted(indices)
# print(indices)
# print(code2inv_file["stats"]["success"])
# print([x[0] for x in failure_candidates])

print("====================== Code2Inv benchmarks ======================")
print("To rerun: ", len(to_rerun))
print("Without houdini: ", len(code2inv_stats["without_houdini"]))
print("With houdini: ", len(code2inv_stats["with_houdini"]))
print("=================================================================")

failure_candidates = []
old_benchmarks_stats = {"without_houdini": {}, "with_houdini": {}}
old_benchmarks10 = json.load(
    open(
        "with_nudges/old_mix/loopy_2023_08_25_13_54_09/final_rechecked_re_filtered.json",
        "r",
    )
)
old_benchmarks5 = json.load(
    open(
        "with_nudges/old_mix/loopy_2023_08_13_23_52_42/final_rechecked_rechecked_re_filtered.json",
        "r",
    )
)

for c5, c10 in zip(old_benchmarks5["logs"], old_benchmarks10["logs"]):
    success = False
    if not ("completions" not in c5 and "completions" not in c10):
        total_completions = ([] if "completions" not in c5 else c5["completions"]) + (
            [] if "completions" not in c10 else c10["completions"]
        )

        if "success" in total_completions[0]:
            any_success = any(
                [completion["success"] for completion in total_completions]
            )
        else:
            raise Exception("No success in completions")

    if any_success:
        success = True
        old_benchmarks_stats["without_houdini"][(c5["file"])] = True
        continue
    else:
        if "checker_output_after_combine_and_prune" in c5:
            if c5["checker_output_after_combine_and_prune"]:
                success = True
                old_benchmarks_stats["with_houdini"][(c5["file"])] = True
                continue
        if "checker_output_after_combine_and_prune" in c10:
            if c10["checker_output_after_combine_and_prune"]:
                success = True
                old_benchmarks_stats["with_houdini"][(c10["file"])] = True

    if not success:
        failure_candidates.append(
            (
                c5["file"],
                c5["benchmark_code"],
                [] if not "invariants" in c5 else c5["invariants"],
                [] if not "invariants" in c10 else c10["invariants"],
            )
        )

max_iters = len(failure_candidates) // 32 + 1

for i in range(0, max_iters):
    Logger.log_info(f"Rechecking {i+1}/{max_iters}")
    benchmarks = failure_candidates[i : i + 32]
    benchmarks_with_file = benchmarks
    invariants = [
        s
        for x in benchmarks
        for s in x[2] + x[3]
        if not s.startswith(
            "ERROR: Output does not contain at least 1 code block\nOutput:"
        )
    ]
    benchmarks = [
        framac_benchmark.combine_llm_outputs(
            x[1], invariants, features="one_loop_one_method"
        )
        for x in benchmarks
    ]
    results = run_parallel(benchmarks, prune_wrapper)
    for benchmark, result in zip(benchmarks_with_file, results):
        benchmark_json = {"file": benchmark[0], "code": benchmark[1]}
        benchmark_json["checker_output"] = result[0]
        benchmark_json["code_with_pruned_annotations"] = result[1]
        rechecking_json["logs"].append(benchmark_json)
        if result[0]:
            Logger.log_success(f"Rechecking {benchmark[0]}: Success")
        else:
            Logger.log_error(f"Rechecking {benchmark[0]}: Failure")

with open("rechecking2.json", "w") as f:
    json.dump(rechecking_json, f, indent=4)


print("====================== Old benchmarks ======================")
print("To rerun: ", len(to_rerun))
print("Without houdini: ", len(old_benchmarks_stats["without_houdini"]))
print("With houdini: ", len(old_benchmarks_stats["with_houdini"]))
print("============================================================")


failure_candidates = []
diff_files_stats = {"without_houdini": [], "with_houdini": []}
diff_files = json.load(
    open("with_nudges/diff_files/loopy_2023_10_27_10_53_58/final.json", "r")
)

for diff_file in diff_files["logs"]:
    success = False
    if "completions" not in diff_file:
        to_rerun[(diff_file["file"])] = True
        continue
    any_success = False
    for completion in diff_file["completions"]:
        if "checker_output_for_annotations" in completion:
            any_success = any_success or completion["checker_output_for_annotations"]

    if any_success:
        success = True
        diff_files_stats["without_houdini"].append(diff_file["file"])
    else:
        if "checker_output_after_prune" in diff_file:
            if diff_file["checker_output_after_prune"]:
                success = True
                diff_files_stats["with_houdini"].append(diff_file["file"])
        else:
            to_rerun[(diff_file["file"])] = True
    if not success:
        failure_candidates.append(
            (diff_file["file"], diff_file["code_with_combined_annotations"])
        )

max_iters = len(failure_candidates) // 32 + 1

for i in range(0, max_iters):
    Logger.log_info(f"Rechecking {i+1}/{max_iters}")
    benchmarks = failure_candidates[i : i + 32]
    benchmarks_with_file = benchmarks
    benchmarks = [x[1] for x in benchmarks]
    results = run_parallel(benchmarks, prune_wrapper)
    for benchmark, result in zip(benchmarks_with_file, results):
        benchmark_json = {"file": benchmark[0], "code": benchmark[1]}
        benchmark_json["checker_output"] = result[0]
        benchmark_json["code_with_pruned_annotations"] = result[1]
        rechecking_json["logs"].append(benchmark_json)
        if result[0]:
            Logger.log_success(f"Rechecking {benchmark[0]}: Success")
        else:
            Logger.log_error(f"Rechecking {benchmark[0]}: Failure")

with open("rechecking3.json", "w") as f:
    json.dump(rechecking_json, f, indent=4)


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

with open("files_to_rerun.txt", "w") as f:
    for file in to_rerun:
        f.write(file + "\n")

# with open("dual_failure_candidates.txt", "w") as f:
#     for file in dual_failing_candidate:
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

import json
import multiprocessing
import os
import sys
import traceback
import random
import copy

sys.path.append(os.path.join(os.path.dirname(__file__), "../src/"))
from frama_c import FramaCChecker, FramaCBenchmark


def shuffle(input_list):
    temp = copy.deepcopy(input_list)
    random.shuffle(temp)
    return temp


def run_parallel(inputs, func):
    assert len(inputs) <= 10

    pool = multiprocessing.Pool(processes=len(inputs))
    results = pool.map(func, inputs)
    pool.close()
    pool.join()
    return results


def prune_wrapper(checker_input):
    checker = FramaCChecker()
    success = False
    pruned_code = ""
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


def check_candidate(checker_input, completions):
    fb = FramaCBenchmark(features="one_loop_one_method")
    for completion in completions:
        if completion["success"]:
            return True, completion["code_with_invariants"]
        if "success_after_prune" in completion and completion["success_after_prune"]:
            return True, completion["pruned_code"]

    invariants = [c["invariants"] for c in completions]
    checker_input_with_invariants = fb.combine_llm_outputs(
        checker_input, invariants, features="one_loop_one_method"
    )
    return prune_wrapper(checker_input_with_invariants)


# first argument is the path to the combined log file

combined_json = json.load(open(sys.argv[1], "r", encoding="utf-8"))
output_path = sys.argv[1].replace(".json", "_processed.json")
start_k = int(sys.argv[2])
end_k = int(sys.argv[3])

main_log = {
    "logs": [],
}

for k in range(start_k, end_k + 1):
    k_log = {
        "k": k,
        "logs": [],
    }
    for benchmark in combined_json["logs"]:
        benchmark_log = {
            "file": benchmark["file"],
            "benchmark_code": benchmark["benchmark_code"],
        }
        completions = benchmark["completions"]
        shufflings = [shuffle(completions) for _ in range(10)]
        candidates = [shuffling[:k] for shuffling in shufflings]
        pass_at_k = None
        for candidate in candidates:
            if any(c["success"] for c in candidate):
                pass_at_k = candidate
                break
        benchmark_log["pass_at_k"] = pass_at_k

        pass_at_k_prune = 0.0
        results = run_parallel(
            [(benchmark["benchmark_code"], candidate) for candidate in candidates],
            check_candidate,
        )

        total_success = sum(r[0] for r in results)
        pass_at_k_prune = total_success / len(results)
        benchmark_log["pass_at_k_prune"] = pass_at_k_prune

        k_log["logs"].append(benchmark_log)

    main_log["logs"].append(k_log)

json.dump(main_log, open(output_path, "w", encoding="utf-8"), indent=4)

import json
import multiprocessing
import os
import sys
import traceback
import random
import copy

sys.path.append(os.path.join(os.path.dirname(__file__), "../src/"))
from frama_c import FramaCChecker, FramaCBenchmark
from llm_utils import Logger


def shuffle(input_list):
    temp = copy.deepcopy(input_list)
    random.shuffle(temp)
    return temp


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

def trivial_check_candidate(checker_input, completions):
    fb = FramaCBenchmark(features="one_loop_one_method")
    for completion in completions:
        if "success" in completion and completion["success"]:
            return (
                True,
                completion["invariants"]
                if not "code_with_invariants" in completion
                else completion["code_with_invariants"],
            )
        if "success_after_prune" in completion and completion["success_after_prune"]:
            return True, completion["pruned_code"]
    return False, ""

def check_candidate(candidate_to_check):
    (checker_input, completions) = candidate_to_check
    fb = FramaCBenchmark(features="one_loop_one_method")
    for completion in completions:
        if "success" in completion and completion["success"]:
            return (
                True,
                completion["invariants"]
                if not "code_with_invariants" in completion
                else completion["code_with_invariants"],
            )
        if "success_after_prune" in completion and completion["success_after_prune"]:
            return True, completion["pruned_code"]
        
    completions_with_invariants = list(filter(lambda c: "invariants" in c, completions))
    if len(completions_with_invariants) == 0:
        return False, ""
    invariants = [c["invariants"] for c in completions_with_invariants]
    checker_input_with_invariants = fb.combine_llm_outputs(
        checker_input, invariants, features="one_loop_one_method"
    )
    return prune_wrapper(checker_input_with_invariants)


# first argument is the path to the combined log file

combined_json = json.load(open(sys.argv[1], "r", encoding="utf-8"))
start_k = int(sys.argv[2])
end_k = int(sys.argv[3])
start_index = int(sys.argv[4])
end_index = int(sys.argv[5])
output_path = (
    sys.argv[1][:-5] + f"_k_{start_k}_{end_k}_index_{start_index}_{end_index}.json"
)

main_log = {
    "logs": [],
}
if start_k == end_k and start_k == 15:
    benchmarks_to_run = []
    pass_at_15 = []
    pass_at_15_prune = []
    pass_at_15_prune_fail = []
    for benchmark in combined_json["logs"][start_index:end_index]:
        for completion in benchmark["completions"]:
            if "success" in completion and completion["success"]:
                pass_at_15.append(benchmark["file"])

        trivial_success, _ =  trivial_check_candidate(benchmark["benchmark_code"], benchmark["completions"])
        if trivial_success:
            pass_at_15_prune.append(benchmark["file"])
            continue
        else:
            benchmarks_to_run.append(benchmark)

    num_cores = 16
    max_iters = (len(benchmarks_to_run) // num_cores) + 1
    for i in range(2, max_iters):
        Logger.log_info(f"Running iteration {i} out of {max_iters}")
        benchmarks = benchmarks_to_run[i * num_cores : (i + 1) * num_cores]
        benchmarks_with_invariants = []
        for benchmark in benchmarks:
            invariants = benchmark["invariants"]
            if len(invariants) == 0:
                with open(datetime.now().strftime("%Y%m%d-%H%M%S") + ".json", "w") as f:
                    f.write(benchmark)
                continue
            final_invariants = []
            for inv in invariants:
                if len(inv) == 2 and inv[0] == "ERROR: Output does not contain at least 1 complete code block":
                    continue
                elif inv.startswith('ERROR: Output does not contain at least 1 code block\nOutput:\n'):
                    continue
                else:
                    final_invariants.append(inv)
            benchmarks_with_invariants.append((benchmark["benchmark_code"], final_invariants))

        fb = FramaCBenchmark(features="one_loop_one_method")
        combined_benchmarks = [
            fb.combine_llm_outputs(benchmark, invariants, features="one_loop_one_method")
            for benchmark, invariants in benchmarks_with_invariants
        ]
        
        results = run_parallel(combined_benchmarks, prune_wrapper)
        for benchmark, result in zip(benchmarks, results):
            if result[0]:
                pass_at_15_prune.append(benchmark["file"])
            else:
                pass_at_15_prune_fail.append(benchmark["file"])
                

    with open("combined_logs_m1_stats_15.json", "w", encoding="utf-8") as f:
        json.dump({
            "pass_at_15": pass_at_15, 
            "pass_at_15_prune": pass_at_15_prune, 
            "pass_at_15_count": len(pass_at_15), 
            "pass_at_15_prune_count" : len(pass_at_15_prune), 
            "prune_fail": pass_at_15_prune_fail,
            "prune_fail_count": len(pass_at_15_prune_fail)
            }, f, indent=4)

    exit(0)


for benchmark in combined_json["logs"][start_index:end_index]:
    benchmark_log = {
        "file": benchmark["file"],
        "benchmark_code": benchmark["benchmark_code"],
        "pass_at_k": {k: 0.0 for k in range(start_k, end_k + 1)},
        "pass_at_k_prune": {k: 0.0 for k in range(start_k, end_k + 1)},
    }
    completions = benchmark["completions"]
    shufflings = [shuffle(completions) for _ in range(10)]

    for k in range(start_k, end_k + 1):
        pass_at_k = 0.0

        candidates = [shuffling[:k] for shuffling in shufflings]
        pass_at_k = 0.0
        for candidate in candidates:
            candidates_with_success = [c for c in candidate if "success" in c]
            if any(c["success"] for c in candidates_with_success):
                pass_at_k += 1.0
        pass_at_k /= len(candidates)

        pass_at_k_prune = 0.0
        results = run_parallel(
            [(benchmark["benchmark_code"], candidate) for candidate in candidates],
            check_candidate,
        )

        total_success = sum(r[0] for r in results)
        pass_at_k_prune = total_success / len(results)

        benchmark_log["pass_at_k"][k] = pass_at_k
        benchmark_log["pass_at_k_prune"][k] = pass_at_k_prune

        Logger.log_info(
            "Benchmark: {} k: {} pass_at_k: {} pass_at_k_prune: {}".format(
                benchmark["file"], k, pass_at_k, pass_at_k_prune
            )
        )

    main_log["logs"].append(benchmark_log)

json.dump(main_log, open(output_path, "w", encoding="utf-8"), indent=4)

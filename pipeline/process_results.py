import argparse
import itertools
import json
import os
import random
import sys
import multiprocessing
import copy

from frama_c import FramaCBenchmark, FramaCChecker
from llm_utils import Logger

max_cores = 32


def get_combinations(input, k):
    temp = list(itertools.combinations(input, k))
    res = []
    for i in temp:
        res.append(list(i))
    return res


def shuffle(input_list):
    temp = copy.deepcopy(input_list)
    random.shuffle(temp)
    return temp


def run_parallel(inputs, func):
    assert len(inputs) <= max_cores

    pool = multiprocessing.Pool(processes=len(inputs))
    results = pool.map(func, inputs)
    pool.close()
    pool.join()
    return results


def prune_wrapper(checker_input):
    checker = FramaCChecker()
    success, pruned_code = checker.prune_annotations_and_check(
        checker_input, features="one_loop_one_method", use_json_output=True
    )
    return success


def check_wrapper(input):
    (benchmark_code, pass_at_k_candidate) = input
    framac_benchmark = FramaCBenchmark(features="one_loop_one_method")
    checker = FramaCChecker()
    for inv_set in pass_at_k_candidate:
        checker_input = framac_benchmark.combine_llm_outputs(
            benchmark_code, [inv_set], "one_loop_one_method"
        )
        success, _ = checker.check(
            checker_input,
            check_variant=("termination" in "one_loop_one_method"),
            use_json_output=True,
        )
        if success:
            return True
    return False


def parse_args(args):
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("--k", type=int, required=True)
    arg_parser.add_argument("--start-k", type=int, required=False, default=1)
    arg_parser.add_argument("--start-index", type=int, required=False, default=0)
    arg_parser.add_argument("--input-log", type=str, required=True)
    arg_parser.add_argument("--input-log-2", type=str, required=True)
    arg_parser.add_argument("--check", action="store_true", required=False)
    arg_parser.add_argument("--shuffle-times", type=int, required=False, default=10)
    return arg_parser.parse_args(args)


def main(args):
    args = parse_args(args)
    expt_log = None
    if not os.path.exists(args.input_log) or not os.path.exists(args.input_log_2):
        print("Input log does not exist.")
        return
    with open(args.input_log, "r") as f:
        expt_log = json.load(f)
    with open(args.input_log_2, "r") as f:
        expt_log_2 = json.load(f)
    output_json = {"params": expt_log["params"], "logs": []}
    output_json["params"]["k"] = args.k
    output_json["params"]["input_log_1"] = args.input_log
    output_json["params"]["input_log_2"] = args.input_log_2

    expt_log = expt_log["logs"]
    expt_log_2 = expt_log_2["logs"]
    features = "one_loop_one_method"
    checker = FramaCChecker()
    framac_benchmark = FramaCBenchmark(features=features)
    logger = Logger()
    if "/final.json" in args.input_log:
        output_log_dir = args.input_log.replace("/final.json", "_processed")
    else:
        output_log_dir = "/".join(args.input_log.split("/")[:-1]) + "_processed"
    if not os.path.exists(output_log_dir):
        os.makedirs(output_log_dir)

    final_output_json = []
    expt_log = expt_log[args.start_index :]
    for k in range(args.start_k, args.k + 1):
        logger.log_info(f"Processing k={k}")
        pass_k_json = {
            "k": k,
            "pass_at_k": 0.0,
            "pass_at_k_prune": 0.0,
            "logs": [],
        }
        for i, benchmark in enumerate(expt_log):
            assert benchmark["file"] == expt_log_2[i + args.start_index]["file"]
            assert (
                benchmark["benchmark_code"]
                == expt_log_2[i + args.start_index]["benchmark_code"]
            )

            logger.log_info(
                f"Processing benchmark num. {i+1}, File: {benchmark['file']}"
            )
            benchmark_code = benchmark["benchmark_code"]
            benchmark_json = {
                "file": benchmark["file"],
                "benchmark_code": benchmark_code,
                "pass_at_k": 0.0,
                "pass_at_k_prune": 0.0,
                "checking_exceptions": [],
                "pruning_exceptions": [],
            }

            if (
                "completions" not in benchmark
                or "completions" not in expt_log_2[i + args.start_index]
            ):
                logger.log_error(
                    f"Completions not found for benchmark: {benchmark['file']}"
                )
                benchmark_json["skip_reason"] = "Completions not found"
                pass_k_json["logs"].append(benchmark_json)
                continue

            if args.check:
                benchmark_json.pop("pass_at_k_prune")
                benchmark_json.pop("pruning_exceptions")

                completion_success_1 = [b["success"] for b in benchmark["completions"]]
                completion_success_2 = [
                    b["success"]
                    for b in expt_log_2[i + args.start_index]["completions"]
                ]
                success_from_completions = completion_success_1 + completion_success_2
                if len(success_from_completions) < args.k:
                    success_from_completions = success_from_completions + [
                        False for _ in range(args.k - len(success_from_completions))
                    ]

                random_permutations = [
                    shuffle(success_from_completions) for _ in range(args.shuffle_times)
                ]
                candidates = [rp[:k] for rp in random_permutations]
                success_candidates = [c for c in candidates if True in c]
                pass_at_k = len(success_candidates) / len(candidates)

                benchmark_json["pass_at_k"] = pass_at_k
                logger.log_info(
                    f"Pass@k={pass_at_k} for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
                pass_k_json["pass_at_k"] += pass_at_k

            else:
                benchmark_json.pop("pass_at_k")
                benchmark_json.pop("checking_exceptions")

                invariants_1 = [b["invariants"] for b in benchmark["completions"]]
                invariants_2 = [
                    b["invariants"]
                    for b in expt_log_2[i + args.start_index]["completions"]
                ]
                invariants_from_completions = invariants_1 + invariants_2

                if len(invariants_from_completions) < args.k:
                    invariants_from_completions = invariants_from_completions + [
                        "\nloop invariant \\false;\n"
                        for _ in range(args.k - len(invariants_from_completions))
                    ]

                random_permutations = [
                    shuffle(invariants_from_completions)
                    for _ in range(args.shuffle_times)
                ]
                candidates = [rp[:k] for rp in random_permutations]

                max_m = (len(candidates) // max_cores) + 1
                pass_k_prune = 0.0
                for m in range(0, max_m):
                    candidates_batch = candidates[m * max_cores : (m + 1) * max_cores]
                    checker_inputs = [
                        framac_benchmark.combine_llm_outputs(
                            benchmark_code, pass_at_k_candidate, features
                        )
                        for pass_at_k_candidate in candidates_batch
                    ]
                    logger.log_action(
                        "Pruning",
                        f"[Batch {m+1}/{max_m}]: {len(candidates_batch)} candidates in parallel, k={k}, for benchmark num. {i+1}, File: {benchmark['file']}",
                    )
                    try:
                        results = run_parallel(checker_inputs, prune_wrapper)
                        pass_k_prune += sum(results)
                        logger.log_info(
                            f"[Batch {m+1}/{max_m}]: Pass@k + Pruning = {pass_k_prune / len(results)} for k={k}, {len(candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
                        )
                    except Exception as e:
                        benchmark_json["pass_at_k_prune"] = 0.0
                        logger.log_error(str(e))
                        benchmark_json["pruning_exceptions"].append("\n" + str(e))

                pass_k_prune = pass_k_prune / len(candidates)
                benchmark_json["pass_at_k_prune"] = pass_k_prune
                logger.log_info(
                    f"Pass@k + Pruning = {pass_k_prune} for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
                pass_k_json["pass_at_k"] += pass_k_prune

            pass_k_json["logs"].append(benchmark_json)

        if args.check:
            with open(
                os.path.join(output_log_dir, f"pass_at_{k}_no_pruning.json"), "w"
            ) as pass_k_json_file:
                json.dump(pass_k_json, pass_k_json_file, indent=4, ensure_ascii=False)
        else:
            with open(
                os.path.join(output_log_dir, f"pass_at_{k}_combine_and_prune.json"), "w"
            ) as pass_k_json_file:
                json.dump(pass_k_json, pass_k_json_file, indent=4, ensure_ascii=False)

        final_output_json.append(pass_k_json)

    if args.check:
        with open(
            os.path.join(output_log_dir, f"final_output_no_prune.json"), "w"
        ) as final_output_json_file:
            json.dump(
                final_output_json, final_output_json_file, indent=4, ensure_ascii=False
            )
    else:
        with open(
            os.path.join(output_log_dir, f"final_output_combine_and_prune.json"), "w"
        ) as final_output_json_file:
            json.dump(
                final_output_json, final_output_json_file, indent=4, ensure_ascii=False
            )


if __name__ == "__main__":
    main(args=sys.argv[1:])

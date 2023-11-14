import argparse
import copy
import itertools
import json
import math
import multiprocessing
import os
import random
import sys
import traceback

import numpy as np

from frama_c import FramaCBenchmark, FramaCChecker
from loopy import Loopy
from llm_utils import Logger

shuffle = Loopy.shuffle
prune_wrapper = Loopy.prune_wrapper
run_parallel = Loopy.run_parallel

max_cores = 32


def get_combinations(input, k):
    temp = list(itertools.combinations(input, k))
    res = []
    for i in temp:
        res.append(list(i))
    return res


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
            use_json_dump_for_invariants=True,
        )
        if success:
            return True
    return False


def pass_at_k_np(n, c, k):
    """
    :param n: total number of samples
    :param c: number of correct samples
    :param k: k in pass@$k$
    """
    if n - c < k:
        return 1.0
    return 1.0 - np.prod(1.0 - k / np.arange(n - c + 1, n + 1))


def parse_args(args):
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("--n", type=int, required=True)
    arg_parser.add_argument("--start-k", type=int, required=False, default=1)
    arg_parser.add_argument("--end-k", type=int, required=False, default=1)
    arg_parser.add_argument("--start-index", type=int, required=False, default=0)
    arg_parser.add_argument("--max-benchmarks", type=int, required=False, default=-1)
    arg_parser.add_argument("--input-log", type=str, required=True)
    arg_parser.add_argument("--input-log1", type=str, required=False)
    arg_parser.add_argument("--input-log-2", type=str, required=True)
    arg_parser.add_argument("--input-log-21", type=str, required=False)
    arg_parser.add_argument("--check", action="store_true", required=False)
    arg_parser.add_argument("--pass-at-k-formula", action="store_true", required=False)
    arg_parser.add_argument("--shuffle-times", type=int, required=False, default=10)
    return arg_parser.parse_args(args)


def main(args):
    args = parse_args(args)
    expt_log = None
    expt_log_1 = None
    expt_log_2 = None
    expt_log_21 = None
    if not os.path.exists(args.input_log) or not os.path.exists(args.input_log_2):
        print("Input log does not exist.")
        return
    with open(args.input_log, "r") as f:
        expt_log = json.load(f)
    if args.input_log1 is not None and os.path.exists(args.input_log1):
        with open(args.input_log1, "r") as f:
            expt_log_1 = json.load(f)
    with open(args.input_log_2, "r") as f:
        expt_log_2 = json.load(f)
    if args.input_log_21 is not None and os.path.exists(args.input_log_21):
        with open(args.input_log_21, "r") as f:
            expt_log_21 = json.load(f)
    output_json = {"params": expt_log["params"], "logs": []}
    output_json["params"]["n"] = args.n
    output_json["params"]["start_k"] = args.start_k
    output_json["params"]["end_k"] = args.end_k
    output_json["params"]["input_log_1"] = args.input_log
    output_json["params"]["input_log_2"] = args.input_log_2

    features = "one_loop_one_method"
    framac_benchmark = FramaCBenchmark(features=features)
    logger = Logger()
    if "/final.json" in args.input_log:
        output_log_dir = args.input_log.replace("/final.json", "_processed")
    else:
        output_log_dir = args.input_log + "_processed"
    if not os.path.exists(output_log_dir):
        os.makedirs(output_log_dir)

    args.max_benchmarks = (
        len(expt_log["logs"]) if args.max_benchmarks == -1 else args.max_benchmarks
    )

    final_output_json = []
    expt_log = expt_log["logs"]
    expt_log = expt_log[args.start_index : args.start_index + args.max_benchmarks]
    expt_log_2 = expt_log_2["logs"]
    expt_log_2 = expt_log_2[args.start_index : args.start_index + args.max_benchmarks]

    if args.input_log1 is not None:
        expt_log_1 = expt_log_1["logs"]
        expt_log_1 = expt_log_1[
            args.start_index : args.start_index + args.max_benchmarks
        ]
    if args.input_log_21 is not None:
        expt_log_21 = expt_log_21["logs"]
        expt_log_21 = expt_log_21[
            args.start_index : args.start_index + args.max_benchmarks
        ]

    final_log = {
        "logs": [],
        "results": {
            k: {"pass_at_k": 0.0, "pass_at_k_prune": 0.0}
            for k in range(args.start_k, args.end_k + 1)
        },
    }
    logs_to_recheck = {}
    failure_at_eight = []
    for i, benchmark in enumerate(expt_log):
        assert benchmark["file"] == expt_log_2[i]["file"]
        assert benchmark["benchmark_code"] == expt_log_2[i]["benchmark_code"]

        if args.input_log1 is not None and expt_log_1 is not None:
            assert benchmark["file"] == expt_log_1[i]["file"]
            assert benchmark["benchmark_code"] == expt_log_1[i]["benchmark_code"]

        if args.input_log_21 is not None and expt_log_21 is not None:
            assert benchmark["file"] == expt_log_21[i]["file"]
            assert benchmark["benchmark_code"] == expt_log_21[i]["benchmark_code"]

        logger.log_info(f"Processing benchmark num. {i+1}, File: {benchmark['file']}")

        benchmark_code = benchmark["benchmark_code"]
        benchmark_json = {
            "file": benchmark["file"],
            "benchmark_code": benchmark_code,
            "pass_at_k": [],
            "pass_at_k_prune": [],
            "checking_exceptions": [],
            "pruning_exceptions": [],
        }

        if (
            "completions" not in benchmark
            or "completions" not in expt_log_2[i]
            or (expt_log_1 is not None and "completions" not in expt_log_1[i])
            or (expt_log_21 is not None and "completions" not in expt_log_21[i])
        ):
            logger.log_error(
                f"Completions not found for benchmark: {benchmark['file']}"
            )
            benchmark_json["skip_reason"] = "Completions not found"
            final_log["logs"].append(benchmark_json)
            continue

        random_permutations = []
        random_permutations_1 = []
        random_permutations_2 = []
        if expt_log_1 is not None and expt_log_21 is not None:
            all_completions_1 = benchmark["completions"] + expt_log_1[i]["completions"]
            all_completions_2 = (
                expt_log_2[i]["completions"] + expt_log_21[i]["completions"]
            )
            if len(all_completions_1) < args.n:
                all_completions_1 = all_completions_1 + [
                    {"success": False, "invariants": "\nloop invariant \\false;\n"}
                    for _ in range(args.n - len(all_completions_1))
                ]
            if len(all_completions_2) < args.n:
                all_completions_2 = all_completions_2 + [
                    {"success": False, "invariants": "\nloop invariant \\false;\n"}
                    for _ in range(args.n - len(all_completions_2))
                ]
            random_permutations_1 = [
                shuffle(all_completions_1) for _ in range(args.shuffle_times)
            ]
            random_permutations_2 = [
                shuffle(all_completions_2) for _ in range(args.shuffle_times)
            ]
        else:
            all_completions = (
                benchmark["completions"]
                + expt_log_2[i]["completions"]
                + ([] if expt_log_1 is None else expt_log_1[i]["completions"])
                + ([] if expt_log_21 is None else expt_log_21[i]["completions"])
            )

            if len(all_completions) < args.n:
                all_completions = all_completions + [
                    {"success": False, "invariants": "\nloop invariant \\false;\n"}
                    for _ in range(args.n - len(all_completions))
                ]

            random_permutations = [
                shuffle(all_completions) for _ in range(args.shuffle_times)
            ]

        pass_at_k = 0.0
        for k in range(args.start_k, args.end_k + 1):
            candidates = []
            if expt_log_1 is None or expt_log_21 is None:
                candidates = [rp[:k] for rp in random_permutations]
            else:
                candidates = []
                for i in range(args.shuffle_times):
                    candidates.append(
                        random_permutations_1[i][: math.ceil(k / 2)]
                        + random_permutations_2[i][: math.floor(k / 2)]
                    )

            candidates_success_map = [
                [c["success"] for c in candidate] for candidate in candidates
            ]
            success_candidates = [
                candidate for candidate in candidates_success_map if any(candidate)
            ]
            pass_at_k = len(success_candidates) / len(candidates_success_map)
            benchmark_json["pass_at_k"].append(pass_at_k)
            logger.log_info(
                f"Pass@k={pass_at_k} for k={k}, for benchmark: {benchmark['file']}"
            )
            final_log["results"][k]["pass_at_k"] += pass_at_k

            candidates_invariants_map = [
                [c["invariants"] for c in candidate] for candidate in candidates
            ]

            max_m = (len(candidates_invariants_map) // max_cores) + 1
            pass_k_prune = 0.0
            for m in range(0, max_m):
                candidates_batch = candidates_invariants_map[
                    m * max_cores : (m + 1) * max_cores
                ]
                checker_inputs = [
                    framac_benchmark.combine_llm_outputs(
                        benchmark_code, pass_at_k_candidate, features
                    )
                    for pass_at_k_candidate in candidates_batch
                ]
                logger.log_action(
                    "Pruning",
                    f"[Batch {m+1}/{max_m}]: {len(candidates_batch)} candidates in parallel, k={k}, for benchmark: {benchmark['file']}",
                )
                try:
                    results = run_parallel(checker_inputs, prune_wrapper)
                    for i in range(len(results) - 1):
                        if results[i] > results[i + 1]:
                            logs_to_recheck[benchmark["file"]] = {
                                "benchmark_code": benchmark_code,
                                "pass_at_k_candidate": candidates_batch,
                                "results": results,
                            }
                    if k == 8 and results[-1] == 0.0:
                        failure_at_eight.append(
                            {
                                "file": benchmark["file"],
                                "benchmark_code": benchmark_code,
                                "pass_at_k_candidate": candidates_batch,
                            }
                        )
                    pass_k_prune += sum(results)
                    logger.log_info(
                        f"[Batch {m+1}/{max_m}]: Combine and Prune with k = {pass_k_prune / len(results)} for k={k}, {len(candidates_batch)} parallel benchmarks, for benchmark: {benchmark['file']}"
                    )
                except Exception as e:
                    logger.log_error(str(e))
                    benchmark_json["pruning_exceptions"].append("\n" + str(e))

            benchmark_json["pass_at_k_prune"].append(
                pass_k_prune / len(candidates_invariants_map)
            )
            logger.log_info(
                f"Combine and Prune with k = {pass_k_prune / len(candidates_invariants_map)} for k={k}, for benchmark: {benchmark['file']}"
            )
            final_log["results"][k]["pass_at_k_prune"] += pass_k_prune / len(
                candidates_invariants_map
            )

        final_log["logs"].append(benchmark_json)
        final_log["files_to_revisit"] = logs_to_recheck
        final_log["failure_at_eight"] = failure_at_eight
        with open(
            os.path.join(
                output_log_dir,
                benchmark["file"]
                .replace(".c", ".json")
                .replace("../", "")
                .replace("/", "__"),
            ),
            "w",
        ) as benchmark_json_file:
            json.dump(benchmark_json, benchmark_json_file, indent=4, ensure_ascii=False)

    with open(
        os.path.join(
            output_log_dir,
            f"final_output_combine_and_prune_k_from_{args.start_k}_to_{args.end_k}.json",
        ),
        "w",
    ) as final_output_json_file:
        json.dump(final_log, final_output_json_file, indent=4, ensure_ascii=False)


if __name__ == "__main__":
    main(args=sys.argv[1:])
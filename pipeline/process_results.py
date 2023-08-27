import argparse
import itertools
import json
import os
import sys
import multiprocessing

from frama_c import FramaCBenchmark, FramaCChecker
from llm_utils import Logger

max_cores = 48


def get_combinations(input, k):
    temp = list(itertools.combinations(input, k))
    res = []
    for i in temp:
        res.append(list(i))
    return res


def prune_wrapper(checker_input):
    checker = FramaCChecker()
    success, pruned_code = checker.prune_annotations_and_check(
        checker_input, features="one_loop_one_method", use_json_output=True
    )
    return (success, pruned_code)


def check_wrapper(checker_input):
    checker = FramaCChecker()
    success, message = checker.check(
        checker_input,
        check_variant=("termination" in "one_loop_oe_method"),
        use_json_output=True,
    )
    return (success, checker_input)


def run_parallel(inputs, func):
    assert len(inputs) <= max_cores

    with multiprocessing.Pool(processes=len(inputs)) as pool:
        results = pool.imap_unordered(func, inputs)

        for result in results:
            if result[0] == True:
                pool.terminate()
                pool.close()
                pool.join()
                return result
    return (False, None)


def parse_args(args):
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("--k", type=int, required=True)
    arg_parser.add_argument("--input-log", type=str, required=True)
    return arg_parser.parse_args(args)


def main(args):
    args = parse_args(args)
    expt_log = None
    if not os.path.exists(args.input_log):
        print("Input log does not exist.")
        return
    with open(args.input_log, "r") as f:
        expt_log = json.load(f)
    output_json = {"params": expt_log["params"], "logs": []}
    output_json["params"]["k"] = args.k
    output_json["params"]["input_log"] = args.input_log

    expt_log = expt_log["logs"]
    features = "one_loop_one_method"
    checker = FramaCChecker()
    framac_benchmark = FramaCBenchmark(features=features)
    logger = Logger()
    for i, benchmark in enumerate(expt_log):
        logger.log_info(f"Processing benchmark no.:{i+1} File: {benchmark['file']}")
        benchmark_json = {}
        benchmark_code = benchmark["benchmark_code"]
        invariants_from_completions = benchmark["invariants"]
        if len(invariants_from_completions) < args.k:
            logger.log_error(
                f"Not enough invariant sets for benchmark: {benchmark['file']}"
            )
            benchmark_json["skip_reason"] = "Not enough invariant sets for benchmark"
            output_json["logs"].append(benchmark_json)
            continue

        benchmark_json["benchmark_code"] = benchmark_code
        benchmark_json["invariants"] = invariants_from_completions
        benchmark_json["pass_k"] = []
        for k in range(1, args.k + 1):
            logger.log_info(
                f"Processing k={k} for benchmark no.:{i+1} File: {benchmark['file']}"
            )
            pass_k_json = {
                "k": k,
                "pass_at_k": False,
                "pass_at_k_success_candidate": None,
                "pass_at_k_combine_prune": False,
                "pass_at_k_combine_prune_success_candidate": None,
                "checking_exceptions": [],
                "pruning_exceptions": [],
            }
            pass_at_k_candidates = get_combinations(invariants_from_completions, k)


            max_j = (len(pass_at_k_candidates) // max_cores) + 1
            for j in range(0, max_j):
                pass_at_k_candidates_batch = pass_at_k_candidates[
                    j * max_cores : (j + 1) * max_cores
                ]
                checker_inputs = [
                    framac_benchmark.combine_llm_outputs(
                        benchmark_code, pass_at_k_candidate, features
                    )
                    for pass_at_k_candidate in pass_at_k_candidates_batch
                ]
                try:
                    logger.log_action(
                        "Checking",
                        f"[Batch {j+1}/{max_j}]: {len(pass_at_k_candidates_batch)} candidates in parallel, k={k}, for benchmark num. {i+1}, File: {benchmark['file']}",
                    )
                    success, success_input = run_parallel(checker_inputs, check_wrapper)
                    if success:
                        pass_k_json["pass_at_k"] = True
                        pass_k_json["pass_at_k_success_candidate"] = success_input
                        break
                    else:
                        logger.log_warning(
                            f"[Batch {j+1}/{max_j}]: Checking failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
                        )
                except Exception as e:
                    logger.log_error(str(e))
                    pass_k_json["checking_exceptions"].append("\n" + str(e))

            if not pass_k_json["pass_at_k"]:
                logger.log_error(
                    f"Pass@k failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
            else:
                logger.log_success(
                    f"Pass@k succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )

            max_m = (len(pass_at_k_candidates) // max_cores) + 1
            for m in range(0, max_m):
                pass_at_k_candidates_batch = pass_at_k_candidates[
                    m * max_cores : (m + 1) * max_cores
                ]
                checker_inputs = [
                    framac_benchmark.combine_llm_outputs(
                        benchmark_code, pass_at_k_candidate, features
                    )
                    for pass_at_k_candidate in pass_at_k_candidates_batch
                ]
                try:
                    logger.log_action(
                        "Pruning",
                        f"[Batch {m+1}/{max_m}]: {len(pass_at_k_candidates_batch)} candidates in parallel, k={k}, for benchmark num. {i+1}, File: {benchmark['file']}",
                    )
                    success, pruned_code = run_parallel(checker_inputs, prune_wrapper)
                    if success:
                        pass_k_json["pass_at_k_combine_prune"] = True
                        pass_k_json[
                            "pass_at_k_combine_prune_success_candidate"
                        ] = pruned_code
                        break
                    else:
                        logger.log_warning(
                            f"[Batch {m+1}/{max_m}]: Pass@k + Pruning failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
                        )
                except Exception as e:
                    logger.log_error(str(e))
                    pass_k_json["pruning_exceptions"].append("\n" + str(e))

            if not pass_k_json["pass_at_k_combine_prune"]:
                logger.log_error(
                    f"Pass@k + Pruning failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
            else:
                logger.log_success(
                    f"Pass@k + Pruning succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )

            benchmark_json["pass_k"].append(pass_k_json)

        output_json["logs"].append(benchmark_json)

    with open(args.input_log.replace(".json", "_processed.json"), "w") as f:
        json.dump(output_json, f, indent=4, ensure_ascii=False)


if __name__ == "__main__":
    main(args=sys.argv[1:])

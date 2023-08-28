import argparse
import itertools
import json
import os
import sys
import multiprocessing

from frama_c import FramaCBenchmark, FramaCChecker
from llm_utils import Logger

max_cores = 32


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
    arg_parser.add_argument("--start-k", type=int, required=False, default=1)
    arg_parser.add_argument("--start-index", type=int, required=False, default=0)
    arg_parser.add_argument("--k", type=int, required=True)
    arg_parser.add_argument("--input-log", type=str, required=True)
    arg_parser.add_argument("--input-log-2", type=str, required=True)
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
    output_log_dir = args.input_log.replace("/final.json", "_processed")
    if not os.path.exists(output_log_dir):
        os.makedirs(output_log_dir)

    final_output_json = []
    for k in range(args.start_k, args.k + 1):
        logger.log_info(f"Processing k={k}")
        pass_k_json = {
            "k": k,
            "pass_at_k": [],
            "pass_at_k_count": 0,
            "pass_at_k_prune": [],
            "pass_at_k_prune_count": 0,
            "checking_exceptions": [],
            "pruning_exceptions": [],
            "logs": [],
        }
        expt_log = expt_log[args.start_index :]
        for i, benchmark in enumerate(expt_log):
            assert benchmark["file"] == expt_log_2[i]["file"]
            assert benchmark["benchmark_code"] == expt_log_2[i]["benchmark_code"]

            logger.log_info(f"Processing benchmark no.:{i+1} File: {benchmark['file']}")
            benchmark_code = benchmark["benchmark_code"]
            benchmark_json = {
                "file": benchmark["file"],
                "benchmark_code": benchmark_code,
                "pass_at_k": False,
                "pass_at_k_success_candidate": None,
                "pass_at_k_prune": False,
                "pass_at_k_prune_success_candidate": None,
                "checking_exception": [],
                "pruning_exceptions": []
            }

            if "completions" not in benchmark or "completions" not in expt_log_2[i]:
                logger.log_error(
                    f"Completions not found for benchmark: {benchmark['file']}"
                )
                benchmark_json["skip_reason"] = "Completions not found"
                pass_k_json["logs"].append(benchmark_json)
                continue

            invariants_1 = [b["invariants"] for b in benchmark["completions"]]
            invariants_2 = [b["invariants"] for b in expt_log_2[i]["completions"]]
            invariants_from_completions = invariants_1 + invariants_2

            if len(invariants_from_completions) < args.k:
                logger.log_error(
                    f"Not enough invariant sets for benchmark: {benchmark['file']}"
                )
                benchmark_json[
                    "skip_reason"
                ] = "Not enough invariant sets for benchmark"
                pass_k_json["logs"].append(benchmark_json)
                continue

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
                        benchmark_json["pass_at_k"] = True
                        benchmark_json["pass_at_k_success_candidate"] = success_input
                        break
                    else:
                        logger.log_warning(
                            f"[Batch {j+1}/{max_j}]: Checking failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
                        )
                except Exception as e:
                    logger.log_error(str(e))
                    benchmark_json["checking_exceptions"].append("\n" + str(e))

            if not benchmark_json["pass_at_k"]:
                logger.log_error(
                    f"Pass@k failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
            else:
                logger.log_success(
                    f"Pass@k succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
                pass_k_json["pass_at_k"].append(benchmark_json["file"])
                pass_k_json["pass_at_k_count"] += 1

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
                        benchmark_json["pass_at_k_prune"] = True
                        benchmark_json[
                            "pass_at_k_prune_success_candidate"
                        ] = pruned_code
                        break
                    else:
                        logger.log_warning(
                            f"[Batch {m+1}/{max_m}]: Pass@k + Pruning failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
                        )
                except Exception as e:
                    logger.log_error(str(e))
                    benchmark_json["pruning_exceptions"].append("\n" + str(e))

            if not benchmark_json["pass_at_k_prune"]:
                logger.log_error(
                    f"Pass@k + Pruning failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
            else:
                logger.log_success(
                    f"Pass@k + Pruning succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
                )
                pass_k_json["pass_at_k_prune"].append(benchmark_json["file"])
                pass_k_json["pass_at_k_prune_count"] += 1

            pass_k_json["logs"].append(benchmark_json)

        logger.log_action(
            "Pass@k",
            f"Pass@k succeeded for {pass_k_json['pass_at_k_count']} benchmarks out of {len(expt_log)} benchmarks",
        )
        logger.log_action(
            "Pass@k + Prune",
            f"Pass@k + Prune succeeded for {pass_k_json['pass_at_k_prune_count']} benchmarks out of {len(expt_log)} benchmarks",
        )

        with open(
            os.path.join(args.output_dir, f"pass_at_{k}.json"), "w"
        ) as pass_k_json_file:
            json.dump(pass_k_json, pass_k_json_file, indent=4, ensure_ascii=False)

        final_output_json.append(pass_k_json)

    with open(
        os.path.join(args.output_dir, f"final_output.json"), "w"
    ) as final_output_json_file:
        json.dump(final_output_json, final_output_json_file, indent=4, ensure_ascii=False)

    # for i, benchmark in enumerate(expt_log):
    #     assert benchmark["file"] == expt_log_2[i]["file"]
    #     assert benchmark["benchmark_code"] == expt_log_2[i]["benchmark_code"]

    #     logger.log_info(f"Processing benchmark no.:{i+1} File: {benchmark['file']}")
    #     benchmark_json = {}
    #     benchmark_code = benchmark["benchmark_code"]
    #     rechecked_invariants = [b["invariants"] for b in benchmark["completions"]]
    #     rechecked_invariants_2 = [b["invariants"] for b in expt_log_2[i]["completions"]]
    #     invariants_from_completions = (
    #         benchmark["invariants"] + expt_log_2[i]["invariants"]
    #     )
    #     if len(invariants_from_completions) < args.k:
    #         logger.log_error(
    #             f"Not enough invariant sets for benchmark: {benchmark['file']}"
    #         )
    #         benchmark_json["skip_reason"] = "Not enough invariant sets for benchmark"
    #         output_json["logs"].append(benchmark_json)
    #         continue

    #     benchmark_json["benchmark_code"] = benchmark_code
    #     benchmark_json["invariants"] = invariants_from_completions
    #     benchmark_json["pass_k"] = []
    #     for k in range(1, args.k + 1):
    #         logger.log_info(
    #             f"Processing k={k} for benchmark no.:{i+1} File: {benchmark['file']}"
    #         )
    #         pass_k_json = {
    #             "k": k,
    #             "pass_at_k": False,
    #             "pass_at_k_success_candidate": None,
    #             "pass_at_k_combine_prune": False,
    #             "pass_at_k_combine_prune_success_candidate": None,
    #             "checking_exceptions": [],
    #             "pruning_exceptions": [],
    #         }
    #         pass_at_k_candidates = get_combinations(invariants_from_completions, k)

    #         max_j = (len(pass_at_k_candidates) // max_cores) + 1
    #         for j in range(0, max_j):
    #             pass_at_k_candidates_batch = pass_at_k_candidates[
    #                 j * max_cores : (j + 1) * max_cores
    #             ]
    #             checker_inputs = [
    #                 framac_benchmark.combine_llm_outputs(
    #                     benchmark_code, pass_at_k_candidate, features
    #                 )
    #                 for pass_at_k_candidate in pass_at_k_candidates_batch
    #             ]
    #             try:
    #                 logger.log_action(
    #                     "Checking",
    #                     f"[Batch {j+1}/{max_j}]: {len(pass_at_k_candidates_batch)} candidates in parallel, k={k}, for benchmark num. {i+1}, File: {benchmark['file']}",
    #                 )
    #                 success, success_input = run_parallel(checker_inputs, check_wrapper)
    #                 if success:
    #                     pass_k_json["pass_at_k"] = True
    #                     pass_k_json["pass_at_k_success_candidate"] = success_input
    #                     break
    #                 else:
    #                     logger.log_warning(
    #                         f"[Batch {j+1}/{max_j}]: Checking failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
    #                     )
    #             except Exception as e:
    #                 logger.log_error(str(e))
    #                 pass_k_json["checking_exceptions"].append("\n" + str(e))

    #         if not pass_k_json["pass_at_k"]:
    #             logger.log_error(
    #                 f"Pass@k failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
    #             )
    #         else:
    #             logger.log_success(
    #                 f"Pass@k succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
    #             )

    #         max_m = (len(pass_at_k_candidates) // max_cores) + 1
    #         for m in range(0, max_m):
    #             pass_at_k_candidates_batch = pass_at_k_candidates[
    #                 m * max_cores : (m + 1) * max_cores
    #             ]
    #             checker_inputs = [
    #                 framac_benchmark.combine_llm_outputs(
    #                     benchmark_code, pass_at_k_candidate, features
    #                 )
    #                 for pass_at_k_candidate in pass_at_k_candidates_batch
    #             ]
    #             try:
    #                 logger.log_action(
    #                     "Pruning",
    #                     f"[Batch {m+1}/{max_m}]: {len(pass_at_k_candidates_batch)} candidates in parallel, k={k}, for benchmark num. {i+1}, File: {benchmark['file']}",
    #                 )
    #                 success, pruned_code = run_parallel(checker_inputs, prune_wrapper)
    #                 if success:
    #                     pass_k_json["pass_at_k_combine_prune"] = True
    #                     pass_k_json[
    #                         "pass_at_k_combine_prune_success_candidate"
    #                     ] = pruned_code
    #                     break
    #                 else:
    #                     logger.log_warning(
    #                         f"[Batch {m+1}/{max_m}]: Pass@k + Pruning failed for k={k}, {len(pass_at_k_candidates_batch)} parallel benchmarks, for benchmark num. {i+1}, File: {benchmark['file']}"
    #                     )
    #             except Exception as e:
    #                 logger.log_error(str(e))
    #                 pass_k_json["pruning_exceptions"].append("\n" + str(e))

    #         if not pass_k_json["pass_at_k_combine_prune"]:
    #             logger.log_error(
    #                 f"Pass@k + Pruning failed for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
    #             )
    #         else:
    #             logger.log_success(
    #                 f"Pass@k + Pruning succeeded for k={k}, for benchmark num. {i+1}, File: {benchmark['file']}"
    #             )

    #         benchmark_json["pass_k"].append(pass_k_json)
    #         with open(
    #             os.path.join(
    #                 output_log_dir,
    #                 benchmark["file"]
    #                 .replace(".c", f"_{k}.json")
    #                 .replace("../", "")
    #                 .replace("/", "__"),
    #             ),
    #             "w",
    #         ) as f:
    #             json.dump(pass_k_json, f, indent=4, ensure_ascii=False)

    #     output_json["logs"].append(benchmark_json)

    # with open(os.path.join(output_log_dir, "final.json"), "w") as f:
    #     json.dump(output_json, f, indent=4, ensure_ascii=False)


if __name__ == "__main__":
    main(args=sys.argv[1:])

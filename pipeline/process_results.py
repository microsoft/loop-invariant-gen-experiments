import argparse
import itertools
import json
import os
import sys
import multiprocessing

from frama_c import FramaCBenchmark, FramaCChecker

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
    success, message = checker.check(checker_input, check_variant=("termination" in "one_loop_oe_method"), use_json_output=True)
    return (success, checker_input)


def prune_parallel(inputs):
    assert len(input) <= max_cores

    with multiprocessing.Pool(processes=len(inputs)) as pool:
        results = pool.imap_unordered(prune_wrapper, inputs)

        for result in results:
            if result[0] == True:
                pool.terminate()
                pool.close()
                pool.join()
                return result
    return (False, None)

def check_parallel(inputs):
    assert len(input) <= max_cores

    with multiprocessing.Pool(processes=len(inputs)) as pool:
        results = pool.imap_unordered(check_wrapper, inputs)

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
    for i, benchmark in enumerate(expt_log):
        print(f"Processing benchmark no.:{i+1} File: {benchmark['file']}")
        benchmark_json = {}
        benchmark_code = benchmark["benchmark_code"]
        invariants_from_completions = benchmark["invariants"]
        if len(invariants_from_completions) < args.k:
            print("Not enough invariant sets for benchmark: ", benchmark_code)
            benchmark_json["skip_reason"] = "Not enough invariant sets for benchmark"
            output_json["logs"].append(benchmark_json)
            continue

        benchmark_json["benchmark_code"] = benchmark_code
        benchmark_json["invariants"] = invariants_from_completions
        benchmark_json["pass_k"] = []
        for k in range(1, args.k + 1):
            print(f"Processing k={k} for benchmark no.:{i+1} File: {benchmark['file']}")
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

            for i in range(0, (len(pass_at_k_candidates) // max_cores) + 1):
                pass_at_k_candidates_batch = pass_at_k_candidates[i * max_cores : (i + 1) * max_cores]
                checker_inputs = [
                    framac_benchmark.combine_llm_outputs(
                        benchmark_code, pass_at_k_candidate, features
                    )
                    for pass_at_k_candidate in pass_at_k_candidates_batch
                ]
                try:
                    print(
                        f"Checking no. candidates in parallel: {len(pass_at_k_candidates_batch)}, k={k} for benchmark no.: {i+1} File: {benchmark['file']}"
                    )
                    success, success_input = check_parallel(checker_inputs)
                    if success:
                        pass_k_json["pass_at_k"] = True
                        pass_k_json[
                            "pass_at_k_success_candidate"
                        ] = success_input
                        print(
                            f"Found check at k={k} for benchmark no.:{i+1} File: {benchmark['file']}"
                        )
                        break
                    else:
                        print(f"Checking failed for {len(pass_at_k_candidates_batch)} parallel benchmarks, k={k} for benchmark no.: {i+1} File: {benchmark['file']}")
                except Exception as e:
                    pass_k_json["checking_exceptions"].append("\n" + str(e))

            for i in range(0, (len(pass_at_k_candidates) // max_cores) + 1):
                pass_at_k_candidates_batch = pass_at_k_candidates[i * max_cores : (i + 1) * max_cores]
                checker_inputs = [
                    framac_benchmark.combine_llm_outputs(
                        benchmark_code, pass_at_k_candidate, features
                    )
                    for pass_at_k_candidate in pass_at_k_candidates_batch
                ]
                try:
                    print(
                        f"Pruning no. candidates in parallel: {len(pass_at_k_candidates_batch)}, k={k} for benchmark no.: {i+1} File: {benchmark['file']}"
                    )
                    success, pruned_code = prune_parallel(checker_inputs)
                    if success:
                        pass_k_json["pass_at_k_combine_prune"] = True
                        pass_k_json[
                            "pass_at_k_combine_prune_success_candidate"
                        ] = pruned_code
                        print(
                            f"Found pass and prune at k={k} for benchmark no.:{i+1} File: {benchmark['file']}"
                        )
                        break
                    else:
                        print(f"Prune and check failed for {len(pass_at_k_candidates_batch)} parallel benchmarks, k={k} for benchmark no.: {i+1} File: {benchmark['file']}")
                except Exception as e:
                    pass_k_json["pruning_exceptions"].append("\n" + str(e))

            benchmark_json["pass_k"].append(pass_k_json)

        output_json["logs"].append(benchmark_json)

    with open(args.input_log.replace(".json", "_processed.json"), "w") as f:
        json.dump(output_json, f, indent=4, ensure_ascii=False)


if __name__ == "__main__":
    main(args=sys.argv[1:])

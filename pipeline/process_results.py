import argparse
import itertools
import json
import os
import sys

from frama_c import FramaCBenchmark, FramaCChecker

def get_combinations(input, k):
    temp = list(itertools.combinations(input, k))
    res = []
    for i in temp:
        res.append(list(i))
    return res


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
    output_json = {"params" : expt_log["params"], "logs" : []}
    output_json["params"]["k"] = args.k
    output_json["params"]["input_log"] = args.input_log

    expt_log = expt_log["logs"]
    features = "one_loop_one_method"
    checker = FramaCChecker()
    framac_benchmark = FramaCBenchmark(features=features)
    for benchmark in expt_log:
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
        for k in range(1, args.k + 1):
            pass_k_json = {
                "k" : k,
                "pass_at_k" : False,
                "pass_at_k_success_candidate" : None,
                "pass_at_k_houdini" : False,
                "pass_at_k_houdini_success_candidate" : None,
                "checking_exceptions" : [],
                "pruning_exceptions" : []
            }
            pass_at_k_candidates = get_combinations(invariants_from_completions, k)
            
            for pass_at_k_candidate in pass_at_k_candidates:
                checker_input = framac_benchmark.combine_llm_outputs(benchmark_code, pass_at_k_candidate, features)
                try:
                    success, checker_message = checker.check(checker_input, check_variant=("termination" in features), use_json_output=True)
                    if success:
                        pass_k_json["pass_at_k"] = True
                        pass_k_json["pass_at_k_success_candidate"] = pass_at_k_candidate
                        break
                except Exception as e:
                    pass_k_json["checking_exceptions"].append("\n" + str(e))
                
            for pass_at_k_candidate in pass_at_k_candidates:
                checker_input = framac_benchmark.combine_llm_outputs(benchmark_code, pass_at_k_candidate, features)
                try:
                    success, pruned_code = checker.prune_annotations_and_check(checker_input, features=features, use_json_output=True)
                    if success:
                        pass_k_json["pass_at_k_houdini"] = True
                        pass_k_json["pass_at_k_houdini_success_candidate"] = pruned_code
                        break
                except Exception as e:
                    pass_k_json["pruning_exceptions"].append("\n" + str(e))

            benchmark_json["pass_k"].append(pass_k_json)

        output_json["logs"].append(benchmark_json)

    with open(args.input_log.replace(".json", "_processed.json"), "w") as f:
        json.dump(output_json, f, indent=4, ensure_ascii=False)              


if __name__ == "__main__":
    main(args=sys.argv[1:])

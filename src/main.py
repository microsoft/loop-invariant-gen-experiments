import argparse
import datetime
import sys

import yaml

from frama_c import FramaCBenchmark, FramaCChecker
from loopy import Benchmark, Checker, LoopyPipeline


def parse_args(args):
    parser = argparse.ArgumentParser()

    # Config file to use. Either provide this, or everything as command line arguments
    parser.add_argument(
        "--config-file",
        help="Config file to use. Specify all params in this file (or as command line args).",
        default="",
        type=str,
    )

    # Checker to use
    parser.add_argument(
        "--checker",
        help="Checker to use [Required]",
        choices=["boogie", "frama-c"],
        default="frama-c",
        type=str,
    )

    # LLM to use
    parser.add_argument(
        "--model",
        help="Model to use",
        choices=["gpt-4", "gpt-3.5-turbo", "gpt-4-32k", "codellama-34b-instruct"],
        default="gpt-4",
        type=str,
    )
    parser.add_argument(
        "--temperature",
        help="Temperature for sampling",
        type=float,
        default=0.7,
    )
    parser.add_argument(
        "--num_completions",
        help="Number of completions to generate",
        type=int,
        default=1,
    )

    # Input can be specified as a directory or a file
    input_group = parser.add_mutually_exclusive_group(required=False)
    input_group.add_argument(
        "--benchmark-file",
        help="Input file containing benchmark file paths (relative to main.py)",
        default="benchmarks.txt",
        type=str,
    )
    input_group.add_argument(
        "--repair-input",
        help="Input file to repair invariants for",
        default="",
        required=False,  # cannot set retries without setting input
        type=str,
    )
    input_group.add_argument(
        "--recheck-input",
        help="Recheck JSON logs from a previous run",
        type=str,
        default="",
    )

    # Output logs directory
    parser.add_argument(
        "--output-dir",
        help="Directory to write output logs to (Each file gets a separate file, and one final file with all logs)",
        default=datetime.datetime.now().strftime("../logs/loopy_%Y_%m_%d_%H_%M_%S/"),
        type=str,
    )

    parser.add_argument(
        "--repair-input-2",
        help="Second input file to repair invariants for",
        default="",
        required=False,  # cannot set retries without setting input
        type=str,
    )
    parser.add_argument(
        "--repair-retries",
        help="Number of retries for each repair run",
        type=int,
        default=5,
        required=False,
    )
    parser.add_argument(
        "--repair-from-k",
        help="Start repairing from kth completion",
        type=int,
        default=0,
        required=False,
    )

    parser.add_argument(
        "--max-benchmarks",
        help="Maximum number of benchmarks to run",
        type=int,
        default=-1,
    )

    benchmark_group = parser.add_mutually_exclusive_group()
    benchmark_group.add_argument(
        "--start-index",
        help="Start the run from a given benchmark index",
        type=int,
        default=0,
    )
    benchmark_group.add_argument(
        "--problem-ids", help="Problem IDs to run", nargs="+", default=[], type=str
    )

    parser.add_argument(
        "--provider",
        help="Provider to fetch the model from",
        choices=["azure-open-ai", "local"],
        default="azure-open-ai",
        type=str,
    )

    parser.add_argument(
        "--benchmark-features",
        help="Benchmarks to run based on features",
        choices=[
            "one_loop_one_method",
            "multiple_loops_one_method",
            # "multiple_loops_multiple_methods",
            "termination_one_loop_one_method",
            # "termination_multiple_loops_one_method",
            # "termination_multiple_loops_multiple_methods",
            "all",
        ],
        default="one_loop_one_method",
        type=str,
    )

    parser.add_argument(
        "-d",
        "--debug",
        help="Debug mode",
        action="store_true",
    )

    parser.add_argument(
        "--json-output",
        help="Use JSON output from the checker",
        action="store_true",
    )

    parser.add_argument(
        "--local-llm-output",
        help="Use a previously generated local LLM output",
        type=str,
        default="",
    )

    parser.add_argument(
        "--classify",
        help="Use the LLM as a classifier",
        action="store_true",
    )
    parser.add_argument(
        "--ground-truth-file",
        help="File containing ground truth labels for the benchmarks",
        type=str,
        default="",
    )

    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    # TODO: Add support for other models/hosts when available
    if args.provider not in ["azure-open-ai", "local"]:
        raise Exception("Only models on Azure Open AI are supported for now")

    p = LoopyPipeline(
        arg_params=vars(args),
        model=args.model,
        debug=args.debug,
        use_json_output=args.json_output,
    )

    p = p.load_config(args.config_file)

    p.run_sequence(max_benchmarks=args.max_benchmarks, start_index=args.start_index)

    return

    if args.provider == "local":
        p.run_local(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            local_llm_output=args.local_llm_output,
        )
        return

    if args.classify:
        p.run_classification(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            ground_truth_file=args.ground_truth_file,
        )
        return

    if args.problem_ids:
        for problem_id in args.problem_ids:
            p.log_path = datetime.datetime.now().strftime(
                f"../logs/loopy_{problem_id}_%Y_%m_%d_%H_%M_%S/"
            )
            p.run(
                max_benchmarks=1,
                start_index=int(problem_id),
            )
    elif args.recheck_input != "":
        p.recheck_logs(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            input_log_path=args.recheck_input,
            output_log_path=args.recheck_input.replace("final", "final_rechecked"),
        )

    else:
        if args.repair_input:
            p.log_path = datetime.datetime.now().strftime(
                f"../logs/repair_loopy_%Y_%m_%d_%H_%M_%S/"
            )
            p.heal(max_benchmarks=args.max_benchmarks, start_index=args.start_index)
        else:
            p.run(
                max_benchmarks=args.max_benchmarks,
                start_index=args.start_index,
            )


if __name__ == "__main__":
    main(sys.argv)

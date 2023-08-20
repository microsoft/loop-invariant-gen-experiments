import argparse
import datetime
import sys

from frama_c import FramaCBenchmark, FramaCChecker
from loopy import Benchmark, Checker, LoopyPipeline


def parse_args(args):
    parser = argparse.ArgumentParser()

    # Config file to use. Either provide this or everything as command line arguments
    parser.add_argument(
        "--config-file",
        help="Config file to use. Specify all params in this file (or as command line args).",
        default="config.yaml",
        type=str,
    )

    # Checker to use
    parser.add_argument(
        "--checker",
        help="Checker to use [Required]",
        choices=["boogie", "frama-c"],
        required=True,
        type=str,
    )

    # LLM to use
    parser.add_argument(
        "--model",
        help="Model to use",
        choices=["gpt-4", "gpt-3.5-turbo", "gpt-4-32k", "llama-2"],
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
        "--benchmark-dir",
        help="Input directory to read benchmarks from (relative to main.py)",
        default="benchmarks/",
        type=str,
    )
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
        required="--repair-retries" in args,  # cannot set retries without setting input
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
        default=datetime.datetime.now().strftime("logs/loopy_%Y_%m_%d_%H_%M_%S/"),
        type=str,
    )

    # Input prompt
    parser.add_argument(
        "--prompt-file",
        help="File to read prompt from. The prompt can refer to the input code.",
        default="",
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
        "--secondary-nudge",
        help="Nudge the model to generate better code",
        action="store_true",
    )
    parser.add_argument(
        "--secondary-nudge-text",
        help="File to read nudge prompt from.",
        default="",
        type=str,
        required="--secondary-nudge" in args,
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
            "all",
        ],
        default="one_loop_one_method",
        type=str,
    )
    parser.add_argument(
        "--find-best-k",
        help="Find the best number of completions",
        action="store_true",
    )

    parser.add_argument(
        "-d",
        "--debug",
        help="Debug mode",
        action="store_true",
    )

    parser.add_argument(
        "--ground-truth",
        help="Run Frama-C with \\true as the invariant",
        action="store_true",
    )

    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    # TODO: Add support for other models/hosts when available
    if args.provider != "azure-open-ai":
        raise Exception("Only models on Azure Open AI are supported for now")

    checker = (
        Checker("boogie")
        if args.checker == "boogie"
        else (FramaCChecker() if args.checker == "frama-c" else None)
    )

    benchmark = (
        Benchmark()
        if args.checker == "boogie"
        else (FramaCBenchmark() if args.checker == "frama-c" else None)
    )

    p = LoopyPipeline(
        benchmark=benchmark,
        checker=checker,
        model=args.model,
        debug=args.debug,
        log_path=args.output_dir,
        repair_errors_input=args.repair_input,
        num_repair_retries=args.repair_retries,
        nudge=args.secondary_nudge,
        features=args.benchmark_features,
        arg_params=vars(args),
        ground_truth=args.ground_truth,
    )
    if args.config_file:
        p = p.load_config(args.config_file)

    if args.problem_ids:
        for problem_id in args.problem_ids:
            p.log_path = datetime.datetime.now().strftime(
                f"logs/loopy_{problem_id}_%Y_%m_%d_%H_%M_%S/"
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
            output_log_path=args.recheck_input.replace(
                "final.json", "final_rechecked.json"
            ),
        )

    elif args.find_best_k:
        p.find_best_k()

    else:
        if args.repair_input:
            p.log_path = datetime.datetime.now().strftime(
                f"logs/repair_loopy_%Y_%m_%d_%H_%M_%S/"
            )
            p.heal(max_benchmarks=args.max_benchmarks, start_index=args.start_index)
        else:
            p.run(
                max_benchmarks=args.max_benchmarks,
                start_index=args.start_index,
            )


if __name__ == "__main__":
    main(sys.argv)

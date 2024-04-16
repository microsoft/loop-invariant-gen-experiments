import argparse
import sys

from loopy import Loopy


def parse_args(args):
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--config-file",
        help="Config file to use. Specify all params in this file.",
        default="",
        type=str,
    )
    parser.add_argument(
        "--no-preprocess",
        help="Do not preprocess the benchmarks",
        action="store_true",
    )
    parser.add_argument(
        "--termination-analysis",
        help="Run termination analysis",
        action="store_true",
    )
    parser.add_argument(
        "--recursive-functions",
        help="Run the benchmarks with recursive functions",
        action="store_true",
    )
    parser.add_argument(
        "--loop-invariants",
        help="Find inductive loop invariants",
        action="store_true",
    )
    parser.add_argument(
        "--loop-invariants-prompt",
        help="Prompt to use for loopy",
        type=str,
        choices=[
            "with_nudges",
            "without_nudges",
            "arrays_simplified",
            "arrays_without_nudges",
            "arrays_with_nudges",
        ],
    )
    parser.add_argument(
        "--repair-invariants",
        help="Repair incorrect invariants",
        action="store_true",
    )
    parser.add_argument(
        "--repair-input",
        help="Input log to repair invariants from",
        type=str,
        default="",
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
        help="Start repairing from k-th completion",
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
    parser.add_argument(
        "--start-index",
        help="Start the run from a given benchmark index",
        type=int,
        default=0,
    )
    parser.add_argument(
        "-d",
        "--debug",
        help="Debug mode",
        action="store_true",
    )

    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    p = Loopy(
        arg_params=vars(args),
    )

    p = p.set_config(args.config_file, args.no_preprocess)

    if args.termination_analysis:
        p.termination_analysis(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
        )
    elif args.recursive_functions:
        p.interprocedural_loop_invariant_analysis(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
        )
    elif args.loop_invariants:
        p.find_loop_invariants(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            prompt=args.loop_invariants_prompt,
        )
    elif args.repair_invariants:
        p.repair_loop_invariants(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            input_log=args.repair_input,
            k=args.repair_from_k,
            num_repairs=args.repair_retries,
        )
    else:
        raise Exception(f"Invalid input args: {vars(args)}")


if __name__ == "__main__":
    main(sys.argv)

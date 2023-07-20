import argparse
import datetime
import sys

from frama_c import FramaCBenchmark, FramaCChecker
from loopy import Benchmark, Checker, LoopyPipeline


def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--checker",
        help="Checker to use",
        choices=["boogie", "frama-c"],
        required=True,
    )
    parser.add_argument(
        "--log-file",
        help="File to write logs to",
        default=datetime.datetime.now().strftime("logs/loopy_%Y_%m_%d_%H_%M_%S.json"),
    )
    parser.add_argument(
        "--config-file",
        help="File to read prompt configs from",
        default="config.yaml",
    )
    parser.add_argument(
        "--model",
        help="Model to use",
        choices=["gpt-4", "gpt-3.5-turbo"],
        default="gpt-3.5-turbo",
    )
    parser.add_argument(
        "--debug",
        help="Debug mode",
        action="store_true",
    )
    parser.add_argument(
        "--heal-errors",
        help="Heal incorrect invariants from a previous run",
        action="store_true",
    )
    parser.add_argument(
        "--heal-errors-input",
        help="Input file to heal errors from",
        default="",
    )
    parser.add_argument(
        "--max-benchmarks",
        help="Maximum number of benchmarks to run",
        type=int,
        default=1,
    )
    parser.add_argument(
        "--start-index",
        help="Start the run from a given benchmark index",
        type=int,
        default=0,
    )

    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    checker = None
    if args.checker == "boogie":
        checker = Checker("boogie")
    elif args.checker == "frama-c":
        checker = FramaCChecker()

    if args.heal_errors and args.heal_errors_input == "":
        raise Exception("Please provide an input file to heal errors from")

    p = LoopyPipeline(
        checker=checker,
        model=args.model,
        debug=args.debug,
        log_path=args.log_file,
        heal_errors=args.heal_errors,
        heal_errors_input=args.heal_errors_input,
    )
    p = p.load_config(args.config_file)
    p.run()


if __name__ == "__main__":
    main(sys.argv)

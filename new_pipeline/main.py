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
    parser.add_argument(
        "--healing-iterations",
        help="Number of retries for each healing run",
        type=int,
        default=5,
    )
    parser.add_argument(
        "--provider",
        help="Provider to fetch the model from",
        choices=["azure-open-ai", "huggingface"],
        default="azure-open-ai",
    )


    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    # TODO: Add support for other models when they are available
    if args.provider != "azure-open-ai":
        raise Exception("Only Azure Open AI models are supported for now")
    
    checker = None
    if args.checker == "boogie":
        checker = Checker("boogie")
    elif args.checker == "frama-c":
        checker = FramaCChecker()

    benchmark = None
    if args.checker == "boogie":
        benchmark = Benchmark()
    elif args.checker == "frama-c":
        benchmark = FramaCBenchmark()

    if args.heal_errors and args.heal_errors_input == "":
        raise Exception("Please provide an input file to heal errors from")

    p = LoopyPipeline(
        benchmark=benchmark,
        checker=checker,
        model=args.model,
        debug=args.debug,
        log_path=args.log_file,
        heal_errors=args.heal_errors,
        heal_errors_input=args.heal_errors_input,
        num_healing_retries=args.healing_iterations,
    )
    p = p.load_config(args.config_file)
    p.run(
        max_benchmarks=args.max_benchmarks,
        start_index=args.start_index,
    )


if __name__ == "__main__":
    main(sys.argv)
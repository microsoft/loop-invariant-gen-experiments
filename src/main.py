import argparse
import datetime
import sys

import yaml

from frama_c import FramaCBenchmark, FramaCChecker
from loopy import Benchmark, Checker, Loopy


def parse_args(args):
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--config-file",
        help="Config file to use. Specify all params in this file (or as command line args).",
        default="",
        type=str,
    )

    parser.add_argument(
        "--local-loopy",
        help="Run local loopy",
        action="store_true",
    )

    parser.add_argument(
        "--termination-analysis",
        help="Run the termination analysis algorithm",
        action="store_true",
    )

    parser.add_argument(
        "--termination-baseline",
        help="Run the termination baseline algorithm",
        action="store_true",
    )

    parser.add_argument(
        "--svcomp-files",
        help="Run the SVCOMP benchmarks",
        action="store_true",
    )

    parser.add_argument(
        "--loop-invariants",
        help="Run the loop invariant analysis algorithm",
        action="store_true",
    )

    parser.add_argument(
        "--loopy-prompt",
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

    # Repair invariants
    parser.add_argument(
        "--repair-invariants",
        help="Repair invariants",
        action="store_true",
    )
    parser.add_argument(
        "--repair-input",
        help="Repair invariants input",
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
        help="Start repairing from kth completion",
        type=int,
        default=0,
        required=False,
    )

    parser.add_argument(
        "--checker",
        help="Checker to use [Required]",
        choices=["boogie", "frama-c"],
        default="frama-c",
        type=str,
    )

    parser.add_argument(
        "--model",
        help="Model to use",
        choices=["gpt-4", "gpt-3.5-turbo", "gpt-4-32k", "codellama-34b-instruct"],
        default="gpt-4",
        type=str,
    )

    parser.add_argument(
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
        "--model-host",
        help="Host identifier for the model",
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
            "termination_one_loop_one_method",
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

    return parser.parse_args(args)


def main(args):
    args = parse_args(args[1:])

    if args.model_host not in ["azure-open-ai", "local"]:
        raise Exception("Only models on Azure Open AI are supported for now")

    p = Loopy(
        arg_params=vars(args),
        model=args.model,
        debug=args.debug,
        use_json_output=args.json_output,
    )

    p = p.set_config(args.config_file)

    if args.local_loopy:
        p.local_loopy(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            local_output=args.local_llm_output,
        )
        return
    
    if args.termination_baseline:
        p.termination_baseline(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
        )
        return

    if args.termination_analysis:
        p.termination_analysis(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
        )
        return

    if args.svcomp_files:
        p.interprocedural_loop_invariant_analysis(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
        )
        return

    if args.loop_invariants:
        p.find_loop_invariants(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            prompt=args.loopy_prompt,
        )
        return

    if args.repair_invariants:
        p.repair_loop_invariants(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            input_log=args.repair_1,
            k=args.repair_from_k,
            num_repairs=args.repair_retries,
        )
        return

    elif args.recheck_input != "":
        p.recheck_logs(
            max_benchmarks=args.max_benchmarks,
            start_index=args.start_index,
            input_log_path=args.recheck_input,
            output_log_path=args.recheck_input.replace("final", "final_rechecked"),
        )

    else:
        raise Exception("No task specified")


if __name__ == "__main__":
    main(sys.argv)

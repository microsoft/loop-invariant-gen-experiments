# Copyright (c) Meta Platforms, Inc. and affiliates.
# This software may be used and distributed according to the terms of the Llama 2 Community License Agreement.

import argparse
import json
import os
import sys
import time
from copy import deepcopy as copy

from llama import Llama
from llm_utils import Logger


def parse_args(args):
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--ckpt_dir",
        type=str,
        default="../../../models/code-llama-src/CodeLlama-34b-Instruct/",
    )
    parser.add_argument(
        "--tokenizer_path",
        type=str,
        default="../../../models/code-llama-src/CodeLlama-34b-Instruct/tokenizer.model",
    )
    parser.add_argument("--inputs", type=str, default="input.json")

    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--top_p", type=float, default=0.95)
    parser.add_argument("--max_seq_len", type=int, default=5000)
    parser.add_argument("--max_batch_size", type=int, default=5)
    parser.add_argument("--num_completions", type=int, default=15)
    parser.add_argument("--max_gen_len", type=int, default=1000)

    return parser.parse_args(args)


def main(args):
    benchmarks = []
    output_log = []

    if not os.path.exists(args.inputs):
        raise ValueError(f"Inputs file {args.inputs} does not exist.")

    with open(args.inputs, "r", encoding="utf-8") as f:
        benchmarks = json.load(f)

    generator = Llama.build(
        ckpt_dir=args.ckpt_dir,
        tokenizer_path=args.tokenizer_path,
        max_seq_len=args.max_seq_len,
        max_batch_size=args.max_batch_size,
    )

    output_log_dir = "../logs/" + args.inputs.replace(".json", "") + "_logs"
    if not os.path.exists(output_log_dir):
        os.makedirs(output_log_dir)

    start_time = time.time()

    local_rank = int(os.environ.get("LOCAL_RANK", 0))

    for i, input in enumerate(benchmarks):
        Logger.log_info(
            f"Generating completions for benchmark {i + 1}/{len(benchmarks)}"
        )
        benchmark_log = copy(input)
        benchmark_log["output"] = []
        benchmark_completions = []

        batch = [input["input"] for _ in range(args.num_completions)]

        for j in range(0, args.num_completions, args.max_batch_size):
            Logger.log_info(
                f"Generating batch {(j // args.max_batch_size) + 1}/{args.num_completions // args.max_batch_size}"
            )
            batch_results = generator.chat_completion(
                batch[j : j + args.max_batch_size],
                max_gen_len=args.max_gen_len,
                temperature=args.temperature,
                top_p=args.top_p,
            )
            benchmark_completions.extend(batch_results)

        benchmark_log["output"].append(benchmark_completions)
        benchmark_log_file = os.path.join(
            output_log_dir,
            input["file"].replace(".c", ".json").replace("../", "").replace("/", "__"),
        )
        with open(
            os.path.join(output_log_dir, benchmark_log_file), "w", encoding="utf-8"
        ) as f:
            json.dump(benchmark_log, f, indent=4, ensure_ascii=False)

        output_log.append(benchmark_log)

    end_time = time.time()

    output_log_file = os.path.join(
        output_log_dir,
        "final.json",
    )
    with open(
        os.path.join(output_log_dir, output_log_file), "w", encoding="utf-8"
    ) as f:
        json.dump(output_log, f, indent=4, ensure_ascii=False)

    print(f"Time taken: {end_time - start_time}")
    print(f"Output written to {output_log_file}.")

    return


if __name__ == "__main__":
    args = parse_args(sys.argv[1:])
    main(args)

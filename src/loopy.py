import datetime
import json
import os
import random
import re
import traceback
from copy import deepcopy
import warnings

import yaml

from benchmark import Benchmark
from checker import Checker
from llm_utils import Logger
from loopy_llm import LLM, Prompt
from frama_c import FramaCBenchmark, FramaCChecker
from process_results import prune_wrapper, run_parallel, shuffle


def combine_and_prune_with_k(
    benchmark,
    benchmark2,
    n,
    k,
    shuffle_times=10,
    max_cores=16,
    combine_llm_output_lambda=None,
    features="one_loop_one_method",
):
    logger = Logger()
    invariants_1 = [b["invariants"] for b in benchmark["completions"]]
    invariants_2 = [b["invariants"] for b in benchmark2["completions"]]
    invariants_from_completions = invariants_1 + invariants_2

    if len(invariants_from_completions) < n:
        invariants_from_completions = invariants_from_completions + [
            "\nloop invariant \\false;\n"
            for _ in range(n - len(invariants_from_completions))
        ]

    random_permutations = [
        shuffle(invariants_from_completions) for _ in range(shuffle_times)
    ]
    candidates = [rp[:k] for rp in random_permutations]

    max_m = (len(candidates) // max_cores) + 1
    pass_k_prune = 0.0
    for m in range(0, max_m):
        candidates_batch = candidates[m * max_cores : (m + 1) * max_cores]
        checker_inputs = [
            combine_llm_output_lambda(
                benchmark["benchmark_code"], pass_at_k_candidate, features
            )
            for pass_at_k_candidate in candidates_batch
        ]
        logger.log_action(
            "Combine and Pruning",
            f"[Batch {m+1}/{max_m}]: {len(candidates_batch)} candidates in parallel, k={k}, File: {benchmark['file']}",
        )
        try:
            results = run_parallel(checker_inputs, prune_wrapper)
            pass_k_prune += sum(results)
            logger.log_info(
                f"[Batch {m+1}/{max_m}]: Combine and Prune with k = {pass_k_prune / len(results)} for k={k}, {len(candidates_batch)} parallel benchmarks, File: {benchmark['file']}"
            )
        except Exception as e:
            logger.log_error(str(e))

    pass_k_prune = pass_k_prune / len(candidates)
    if pass_k_prune == 0.0:
        return 0.0, random.choice(candidates)
    else:
        return pass_k_prune, None


class LoopyPipeline:
    def __init__(
        self,
        benchmark: Benchmark = None,
        checker: Checker = Checker("boogie"),
        model: str = "gpt-4",
        debug: bool = False,
        log_path: str = None,
        num_repair_retries: int = 5,
        repair_errors_input: str = "",
        repair_errors_input_2: str = "",
        repair_from_k: int = 1,
        analysis: str = "one_loop_one_method",
        arg_params: dict = None,
        ground_truth: bool = False,
        use_json_output: bool = False,
    ):
        self.benchmark = benchmark
        self.checker = checker
        self.model = model
        self.debug = debug
        self.log_path = log_path
        self.benchmark_features = ""
        self.steps = []

        self.num_repair_retries = num_repair_retries
        self.repair_errors_input = repair_errors_input
        self.repair_errors_input_2 = repair_errors_input_2
        self.repair_from_k = repair_from_k
        self.system_message = ""
        self.analysis = analysis
        self.arg_params = arg_params
        self.use_json_output = use_json_output

    def load_config(self, config_file):
        config = yaml.load(open(config_file, "r"), Loader=yaml.FullLoader)

        if "analysis" in config:
            self.analysis = config["analysis"]

        if not "benchmarks" in config:
            raise Exception("No benchmarks found in config file")
        benchmarks = config["benchmarks"]

        if "benchmark_features" in config:
            self.benchmark_features = config["benchmark_features"]
        else:
            self.benchmark_features = "one_loop_one_method"

        if not "checker" in config:
            raise Exception("No checker found in config file")

        if config["checker"] == "frama-c":
            self.benchmark = FramaCBenchmark(
                benchmarks_file=benchmarks, features=self.benchmark_features
            )
            self.checker = FramaCChecker()
        elif config["checker"] == "boogie":
            warnings.warn(
                "Boogie checker integration might not fully work, use Frama-C instead",
                UserWarning,
            )
            self.benchmark = Benchmark(
                benchmarks_file=benchmarks, features=self.benchmark_features
            )
            self.checker = Checker("boogie")
        else:
            raise Exception(f"Invalid checker: {config['checker']}")

        if not "loopy_sequence" in config:
            raise Exception("No Loopy sequence found in config file")

        for step in config["loopy_sequence"]:
            if type(step) == dict:
                assert len(step.keys()) == 1 and list(step.keys())[0] in [
                    "prompt_llm",
                    "repair_llm",
                ], "Invalid dict step in loopy sequence"
                if list(step.keys())[0] == "prompt_llm":
                    prompt = Prompt().from_file(step["prompt_llm"])
                    annotation_type = step["prompt_llm"]["extract_annotation"]
                    self.steps.append(
                        {"prompt": prompt, "annotation_type": annotation_type}
                    )
                else:
                    prompt = Prompt().from_file(step["repair_llm"])
                    annotation_type = step["repair_llm"]["extract_annotation"]
                    self.steps.append(
                        {
                            "repair": prompt,
                            "annotation_type": annotation_type,
                            "num_retries": step["repair_llm"]["num_retries"],
                        }
                    )
            elif type(step) == str:
                self.steps.append(step)
            else:
                raise Exception("Invalid step type in loopy sequence")

        self.llm = LLM(
            self.model,
            self.debug,
        )

        self.benchmark.check_input()

        return self

    def run(self, max_benchmarks=1, start_index=0):
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        log_json = []
        stats = {"success": [], "failure": [], "skipped": [], "total": 0}

        # create logs dir
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))

        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")

        sliced_benchmarks = self.benchmark.input_file_paths[
            start_index : start_index + max_benchmarks
        ]

        # TODO: Add support for other analysis types
        if (
            self.analysis != "one_loop_one_method"
            and self.analysis != "termination_one_loop_one_method"
        ):
            raise Exception("Unsupported analysis type")

        # Loop through all benchmarks
        for i, instance in enumerate(sliced_benchmarks):
            Logger.log_info(
                f"Running benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}"
            )
            instance_log_json = {
                "file": instance,
                "benchmark_code": self.benchmark.get_code(instance),
                "success": False,
            }

            try:
                llm_outputs = None
                conversations = None

                # Make the LLM query and get the code blocks, and the conversation
                llm_outputs, conversations = self.llm.generate_annotation(
                    {"code": self.benchmark.get_code(instance)}
                )
                instance_log_json["llm_conversation"] = conversations
                instance_log_json["invariants"] = llm_outputs

                # Check each completion individually
                completions = []
                for j, llm_output in enumerate(llm_outputs):
                    Logger.log_info(
                        f"Checking completion {j + 1}/{len(llm_outputs)} for benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}"
                    )

                    completion = {"num_solver_calls": 0, "success": False}

                    # If the completion does not have a code block,
                    # mark it as a failure and continue
                    if len(llm_output) == 2 and llm_output[0] == (
                        "ERROR: Output does not contain at least 1 code block"
                    ):
                        completion["success"] = False
                        completion["llm_output"] = llm_output[1]
                        completion[
                            "error"
                        ] = "Output does not contain at least 1 code block"
                        continue

                    # Add only the loop invariants to the code and check
                    checker_input_with_invariants = self.benchmark.combine_llm_outputs(
                        self.benchmark.get_code(instance),
                        [
                            llm_output
                            if not (
                                len(llm_output) == 2
                                and llm_output[0]
                                == "ERROR: Output does not contain at least 1 code block"
                            )
                            else ""
                        ],
                        "one_loop_one_method",
                    )
                    completion["annotations"] = llm_output
                    completion[
                        "code_with_loop_invariants"
                    ] = checker_input_with_invariants
                    success, checker_message = self.checker.check(
                        checker_input_with_invariants,
                        False,
                        use_json_output=self.use_json_output,
                    )

                    completion["num_solver_calls"] += 1
                    completion["checker_output_for_invariants"] = success
                    completion["checker_message_for_invariants"] = checker_message
                    completion["success"] = completion["success"] or success

                    # If checking failed, try Houdini loop with invariants only
                    if not success:
                        (
                            success,
                            pruned_code,
                            num_frama_c_calls,
                        ) = self.checker.prune_annotations_and_check(
                            checker_input_with_invariants,
                            "one_loop_one_method",
                            use_json_output=self.use_json_output,
                        )
                        completion["num_solver_calls"] += num_frama_c_calls
                        completion[
                            "code_with_loop_invariants_after_prune"
                        ] = pruned_code
                        completion["checker_output_after_prune"] = success
                        completion["success"] = completion["success"] or success

                        checker_input_with_invariants = pruned_code

                    # If termination checking is enabled,
                    # add the variants to the pruned code and check
                    if self.analysis == "termination_one_loop_one_method":
                        Logger.log_info("Checking termination")
                        completion["success"] = False
                        completion["candidates"] = []
                        invariants = self.benchmark.extract_loop_invariants(
                            checker_input_with_invariants
                        )
                        checker_inputs_with_variants = self.benchmark.combine_llm_outputs(
                            self.benchmark.get_code(instance),
                            (
                                invariants,
                                [
                                    llm_output
                                    if not (
                                        len(llm_output) == 2
                                        and llm_output[0]
                                        == "ERROR: Output does not contain at least 1 code block"
                                    )
                                    else ""
                                ],
                            ),
                            "termination_one_loop_one_method",
                        )
                        for checker_input in checker_inputs_with_variants:
                            success, checker_message = self.checker.check(
                                checker_input,
                                True,
                                use_json_output=self.use_json_output,
                            )
                            candidate_with_variant = {}
                            candidate_with_variant[
                                "candidate_with_variant"
                            ] = checker_input
                            candidate_with_variant["checker_output"] = success
                            candidate_with_variant["checker_message"] = checker_message
                            completion["success"] = completion["success"] or success

                            completion["num_solver_calls"] += 1
                            completion["candidates"].append(candidate_with_variant)

                    instance_log_json["success"] = (
                        instance_log_json["success"] or completion["success"]
                    )
                    if completion["success"]:
                        Logger.log_success(f"Checking completion succeeded")
                    else:
                        Logger.log_error(f"Checking completion failed")
                    completions.append(completion)

                # Check the combined completions
                instance_log_json["completions"] = completions
                instance_log_json["individual_completions_num_solver_calls"] = sum(
                    [c["num_solver_calls"] for c in completions]
                )
                instance_log_json["combined_annotation_num_solver_calls"] = 0
                instance_log_json["candidates"] = []
                instance_log_json["combined_candidates"] = []

                Logger.log_info(
                    f"Checking combined completions for benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}"
                )

                # First combine only the loop invariants and check
                code_with_combined_invariants = self.benchmark.combine_llm_outputs(
                    self.benchmark.get_code(instance),
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not (
                            len(llm_output) == 2
                            and llm_output[0]
                            == "ERROR: Output does not contain at least 1 code block"
                        )
                    ],
                    "one_loop_one_method",
                )
                success, checker_message = self.checker.check(
                    code_with_combined_invariants,
                    False,
                    use_json_output=self.use_json_output,
                )

                instance_log_json["combined_annotation_num_solver_calls"] += 1
                instance_log_json[
                    "code_with_combined_invariants"
                ] = code_with_combined_invariants
                instance_log_json["checker_output_for_combined_invariants"] = success
                instance_log_json[
                    "checker_message_for_combined_invariants"
                ] = checker_message
                instance_log_json["success"] = instance_log_json["success"] or success

                # If checking failed, try Houdini loop with combined loop invariants only
                if not success:
                    (
                        success,
                        pruned_code,
                        num_frama_c_calls,
                    ) = self.checker.prune_annotations_and_check(
                        code_with_combined_invariants,
                        "one_loop_one_method",
                        use_json_output=self.use_json_output,
                    )
                    instance_log_json[
                        "combined_annotation_num_solver_calls"
                    ] += num_frama_c_calls
                    instance_log_json[
                        "code_with_combined_invariants_after_prune"
                    ] = pruned_code
                    instance_log_json["checker_output_after_prune"] = success
                    instance_log_json["success"] = (
                        instance_log_json["success"] or success
                    )

                    code_with_combined_invariants = pruned_code

                # If termination checking is enabled,
                # add the variants to the pruned code and check
                if self.analysis == "termination_one_loop_one_method":
                    Logger.log_info("Checking termination")
                    instance_log_json["success"] = False
                    invariants = self.benchmark.extract_loop_invariants(
                        code_with_combined_invariants
                    )
                    checker_inputs = self.benchmark.combine_llm_outputs(
                        self.benchmark.get_code(instance),
                        (
                            invariants,
                            [
                                llm_output
                                for llm_output in llm_outputs
                                if not (
                                    len(llm_output) == 2
                                    and llm_output[0]
                                    == "ERROR: Output does not contain at least 1 code block"
                                )
                            ],
                        ),
                        "termination_one_loop_one_method",
                    )

                    # Check each combined completion individually
                    # with different variant each time
                    for checker_input in checker_inputs:
                        success, checker_message = self.checker.check(
                            checker_input,
                            True,
                            use_json_output=self.use_json_output,
                        )
                        combined_candidate_with_variant = {}
                        combined_candidate_with_variant[
                            "candidate_with_combined_invariants_and_variant"
                        ] = checker_input
                        combined_candidate_with_variant["checker_output"] = success
                        combined_candidate_with_variant[
                            "checker_message"
                        ] = checker_message
                        instance_log_json["success"] = (
                            instance_log_json["success"] or success
                        )

                        instance_log_json["combined_annotation_num_solver_calls"] += 1
                        instance_log_json["combined_candidates"].append(
                            combined_candidate_with_variant
                        )

                if instance_log_json["success"]:
                    Logger.log_success(f"Checking combined annotation succeeded")
                    stats["success"].append(instance_log_json["file"])
                else:
                    Logger.log_error(f"Checking combined annotation failed")
                    stats["failure"].append(instance_log_json["file"])
                stats["total"] += 1

                stats["success_rate"] = (
                    len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
                )

                with open(
                    os.path.join(
                        self.log_path,
                        instance.replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
            except (Exception, KeyboardInterrupt) as e:
                Logger.log_error(traceback.format_exc())
                instance_log_json["error"] = str(e)
                stats["skipped"].append(instance_log_json["file"])
                with open(
                    os.path.join(
                        self.log_path,
                        instance.replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        stats["success_rate"] = (
            len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
        )
        stats["success_count"] = len(stats["success"])
        stats["failure_count"] = len(stats["failure"])
        stats["skipped_count"] = len(stats["skipped"])

        log_file.write(
            json.dumps(
                {"params": self.arg_params, "logs": log_json, "stats": stats},
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

        return

    def heal(self, max_benchmarks=1, start_index=0):
        """
        TODO: Track solver calls
        """
        logger = Logger()
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        error_logs = None
        with open(self.repair_errors_input, "r", encoding="utf-8") as f:
            error_logs = json.load(f)

        error_logs_2 = None
        if self.repair_errors_input_2 != "":
            with open(self.repair_errors_input_2, "r", encoding="utf-8") as f:
                error_logs_2 = json.load(f)

        error_logs = error_logs["logs"][start_index : start_index + max_benchmarks]

        if error_logs_2 is not None:
            error_logs_2 = error_logs_2["logs"][
                start_index : start_index + max_benchmarks
            ]

        log_json = []
        stats = {"success": [], "failure": [], "total": 0}
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))
        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")
        for i, instance in enumerate(error_logs):
            assert instance["file"] == error_logs_2[i]["file"]
            if (
                "completions" not in instance.keys()
                or "completions" not in error_logs_2[i].keys()
            ):
                logger.log_error(
                    f"Skipping benchmark with empty logs: {start_index + i + 1}/{len(error_logs)}"
                )
                stats["total"] += 1
                continue

            prune_and_check_with_k, failing_invariants = combine_and_prune_with_k(
                instance,
                error_logs_2[i],
                15,
                self.repair_from_k,
                combine_llm_output_lambda=self.benchmark.combine_llm_outputs,
                features=self.analysis,
            )
            if prune_and_check_with_k > 0.0:
                logger.log_success(
                    f"Skipping successful benchmark: {start_index + i + 1}/{len(error_logs)}"
                )
                stats["success"].append(i)
                stats["total"] += 1
                continue

            logger.log_info(
                f"Healing benchmark: {start_index + i + 1}/{len(error_logs)}"
            )
            instance_log_json = {"file": instance["file"]}
            try:
                success = False
                num_retries = 0
                instance_log_json["healing_conversations"] = []

                failed_checker_input = self.benchmark.combine_llm_outputs(
                    instance["benchmark_code"],
                    failing_invariants,
                    self.analysis,
                )
                success, checker_error_message = self.checker.check(
                    failed_checker_input,
                    ("termination" in self.analysis),
                    use_json_output=self.use_json_output,
                )

                instance_log_json["code_with_failing_invariants"] = failed_checker_input
                instance_log_json["checker_fail_error_message"] = checker_error_message
                instance_log_json["num_solver_calls"] = 0

                while not success and num_retries < self.num_repair_retries:
                    healing_json = {}
                    llm_outputs, conversations = self.llm.heal(
                        input={
                            "code": failed_checker_input,
                            "error": checker_error_message,
                        },
                        output_full_tree=True,
                    )

                    checker_input = self.benchmark.combine_llm_outputs(
                        instance["benchmark_code"],
                        llm_outputs,
                        self.analysis,
                    )
                    success, checker_message = self.checker.check(
                        checker_input,
                        ("termination" in self.analysis),
                        use_json_output=self.use_json_output,
                    )

                    healing_json["num_solver_calls"] = 1
                    healing_json["conversation"] = conversations.get_full_tree()
                    healing_json["invariants"] = llm_outputs
                    healing_json["benchmark_code"] = instance["benchmark_code"]
                    healing_json["code_with_old_invariants"] = instance[
                        "code_with_combined_invariants"
                    ]
                    healing_json["input_error_message"] = instance["checker_message"]
                    healing_json["code_with_new_invariants"] = checker_input
                    healing_json["checker_output"] = success
                    healing_json["checker_message"] = checker_message

                    if not success:
                        (
                            success,
                            pruned_code,
                            num_solver_calls,
                        ) = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.analysis,
                            use_json_output=self.use_json_output,
                        )
                        success, prune_checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.analysis),
                            use_json_output=self.use_json_output,
                        )
                        healing_json["code_after_combine_and_prune"] = pruned_code
                        healing_json["checker_output_after_combine_and_prune"] = success
                        healing_json[
                            "checker_message_after_combine_and_prune"
                        ] = prune_checker_message
                        healing_json["num_solver_calls"] += num_solver_calls

                        failed_checker_input = checker_input
                        checker_error_message = checker_message

                    instance_log_json["num_solver_calls"] += healing_json[
                        "num_solver_calls"
                    ]
                    instance_log_json["healing_conversations"].append(healing_json)
                    num_retries += 1

                if not success:
                    (
                        success,
                        pruned_code,
                        num_solver_calls,
                    ) = self.checker.prune_annotations_and_check(
                        checker_input,
                        self.analysis,
                        use_json_output=self.use_json_output,
                    )
                    success, prune_checker_message = self.checker.check(
                        pruned_code,
                        ("termination" in self.analysis),
                        use_json_output=self.use_json_output,
                    )
                    healing_json["code_after_heal_and_prune"] = pruned_code
                    healing_json["checker_output_after_heal_and_prune"] = success
                    healing_json[
                        "checker_message_after_heal_and_prune"
                    ] = prune_checker_message

                if success:
                    stats["success"].append(i)
                else:
                    stats["failure"].append(i)
                stats["total"] += 1

                stats["success_rate"] = (
                    len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
                )

                with open(
                    os.path.join(
                        self.log_path,
                        instance["file"]
                        .replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
            except (Exception, KeyboardInterrupt) as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                log_json.append(instance_log_json)
                stats["failure"].append(i)
                stats["total"] += 1
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        stats["success_rate"] = (
            len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
        )

        log_file.write(
            json.dumps(
                {
                    "params": self.arg_params,
                    "logs": log_json,
                    "stats": stats,
                },
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

        return

    def recheck_logs(
        self, max_benchmarks=1, start_index=0, input_log_path="", output_log_path=""
    ):
        # Rerun only the checker on the logs and generate new logs
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        if output_log_path == "":
            output_log_path = self.log_path

        existing_log_json = None
        # Load existing log file. Throws error if it doesn't exist
        with open(input_log_path, "r", encoding="utf-8") as f:
            existing_log_json = json.load(f)

        log_json = []

        stats = {"success": [], "failure": [], "skipped": [], "total": 0}
        log_file = open(output_log_path, "w", encoding="utf-8")
        benchmark_subset = existing_log_json["logs"][
            start_index : start_index + max_benchmarks
        ]
        total = len(benchmark_subset)
        for i, instance in enumerate(benchmark_subset):
            if "completions" not in instance.keys():
                stats["skipped"].append(i)
                log_json.append(instance)
                continue

            print(
                "Rechecking benchmark: {i}/{n}".format(i=start_index + i + 1, n=total)
            )
            instance_log_json = deepcopy(instance)
            try:
                success = False
                if not "benchmark_code" in instance:
                    log_json.append(instance)
                    print(
                        "Skipping benchmark: {i}/{n}".format(
                            i=start_index + i + 1, n=total
                        )
                    )
                    continue
                checker_input_without_invariants = instance["benchmark_code"]

                if not "llm_conversation" in instance:
                    log_json.append(instance)
                    print(
                        "Skipping benchmark: {i}/{n}".format(
                            i=start_index + i + 1, n=total
                        )
                    )
                    continue
                llm_outputs = [
                    self.llm.extract_code(x["content"])
                    for x in instance["llm_conversation"][-1]
                ]

                completions = []
                for j, llm_output in enumerate(llm_outputs):
                    print(f"Checking completion {j + 1}/{len(llm_outputs)}")
                    completion = {}
                    if llm_output.startswith(
                        "ERROR: Output does not contain at least 1 code block"
                    ):
                        completion["success"] = False
                        completion["llm_output"] = llm_output.replace(
                            "ERROR: Output does not contain at least 1 code block\nOutput:\n",
                            "",
                        )
                        completion[
                            "error"
                        ] = "Output does not contain at least 1 code block"
                        continue

                    checker_input = self.benchmark.combine_llm_outputs(
                        instance["benchmark_code"],
                        [llm_output if not llm_output.startswith("ERROR") else ""],
                        self.analysis,
                    )
                    completion["invariants"] = llm_output
                    completion["code_with_invariants"] = checker_input
                    success, checker_message = self.checker.check(
                        checker_input,
                        ("termination" in self.analysis),
                        use_json_output=self.use_json_output,
                    )
                    completion["success"] = success
                    completion["checker_message"] = checker_message

                    if not success:
                        print(f"Pruning completion {j + 1}/{len(llm_outputs)}")
                        try:
                            (
                                success,
                                pruned_code,
                            ) = self.checker.prune_annotations_and_check(
                                checker_input,
                                self.analysis,
                                use_json_output=self.use_json_output,
                            )
                            success, checker_message = self.checker.check(
                                pruned_code,
                                ("termination" in self.analysis),
                                use_json_output=self.use_json_output,
                            )
                            completion["success_after_prune"] = success
                            completion["pruned_code"] = pruned_code
                            completion["checker_message_after_prune"] = checker_message
                        except Exception as e:
                            print(e)
                            print(traceback.format_exc())
                            completion["success_after_prune"] = False
                            completion["pruned_code"] = checker_input
                            completion["checker_message_after_prune"] = e.args[0]
                            success = False

                    completions.append(completion)

                instance_log_json["completions"] = completions

                print(f"Checking combined completion")
                checker_input = self.benchmark.combine_llm_outputs(
                    instance["benchmark_code"],
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not llm_output.startswith(
                            "ERROR: Output does not contain at least 1 code block"
                        )
                    ],
                    self.analysis,
                )
                success, checker_message = self.checker.check(
                    checker_input,
                    ("termination" in self.analysis),
                    use_json_output=self.use_json_output,
                )

                instance_log_json["code_with_combined_invariants"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    print("Pruning combined completion")
                    try:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.analysis,
                            use_json_output=self.use_json_output,
                        )
                        success, checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.analysis),
                            use_json_output=self.use_json_output,
                        )
                        instance_log_json["code_after_combine_and_prune"] = pruned_code
                        instance_log_json[
                            "checker_output_after_combine_and_prune"
                        ] = success
                        instance_log_json[
                            "checker_message_after_combine_and_prune"
                        ] = checker_message
                    except Exception as e:
                        print(e)
                        instance_log_json[
                            "checker_output_after_combine_and_prune"
                        ] = False
                        instance_log_json[
                            "code_after_combine_and_prune"
                        ] = checker_input
                        instance_log_json[
                            "checker_message_after_combine_and_prune"
                        ] = e.args[0]
                        success = False

                if success:
                    stats["success"].append(i)
                else:
                    stats["failure"].append(i)
                stats["total"] += 1

                log_json.append(instance_log_json)
            except (Exception, KeyboardInterrupt) as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                log_json.append(instance_log_json)
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        stats["success_rate"] = (
            len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
        )

        stats["success_count"] = len(stats["success"])
        stats["failure_count"] = len(stats["failure"])
        stats["skipped_count"] = len(stats["skipped"])

        log_file.write(
            json.dumps(
                {"params": self.arg_params, "logs": log_json, "stats": stats},
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

    def run_local(self, max_benchmarks=1, start_index=0, local_llm_output=""):
        """
        TODO: Track solver calls
        """
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        log_json = []
        stats = {"success": [], "failure": [], "skipped": [], "total": 0}

        # create logs dir
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))
        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")

        sliced_benchmarks = self.benchmark.input_file_paths[
            start_index : start_index + max_benchmarks
        ]

        sliced_benchmarks = [
            (instance, {"code": self.benchmark.get_code(instance)})
            for instance in sliced_benchmarks
        ]

        if local_llm_output == "":
            outputs = self.llm.generate_annotations_local(sliced_benchmarks)
        else:
            with open(local_llm_output, "r", encoding="utf-8") as f:
                outputs = json.load(f)
                outputs = outputs[start_index : start_index + max_benchmarks]
                if not ("input" in outputs[0] and "output" in outputs[0]):
                    for i, output in enumerate(outputs):
                        outputs[i] = {
                            "file": sliced_benchmarks[i][0],
                            "input": output[:2],
                            "output": output[2:][0],
                        }

        for i, instance in enumerate(sliced_benchmarks):
            assert instance[0] == outputs[i]["file"]
            print(f"Checking benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}")

            llm_outputs = [
                self.llm.extract_code(c["content"]) for c in outputs[i]["output"]
            ]

            instance_log_json = {
                "file": instance,
                "benchmark_code": self.benchmark.get_code(instance[0]),
                "llm_conversation": outputs[i]["input"] + outputs[i]["output"],
                "invariants": llm_outputs,
            }

            completions = []
            try:
                for j, llm_output in enumerate(llm_outputs):
                    print(f"Checking completion {j + 1}/{len(llm_outputs)}")
                    completion = {}
                    if llm_output.startswith(
                        "ERROR: Output does not contain at least 1 code block"
                    ):
                        completion["success"] = False
                        completion["llm_output"] = llm_output.replace(
                            "ERROR: Output does not contain at least 1 code block\nOutput:\n",
                            "",
                        )
                        completion[
                            "error"
                        ] = "Output does not contain at least 1 code block"
                        continue

                    checker_input = self.benchmark.combine_llm_outputs(
                        self.benchmark.get_code(instance[0]),
                        [llm_output if not llm_output.startswith("ERROR") else ""],
                        self.analysis,
                    )
                    completion["invariants"] = llm_output
                    completion["code_with_invariants"] = checker_input
                    success, checker_message = self.checker.check(
                        checker_input,
                        ("termination" in self.analysis),
                        use_json_output=self.use_json_output,
                    )
                    completion["success"] = success
                    completion["checker_message"] = checker_message

                    if not success:
                        print(f"Pruning completion {j + 1}/{len(llm_outputs)}")
                        try:
                            (
                                success,
                                pruned_code,
                            ) = self.checker.prune_annotations_and_check(
                                checker_input,
                                self.analysis,
                                use_json_output=self.use_json_output,
                            )
                            success, checker_message = self.checker.check(
                                pruned_code,
                                ("termination" in self.analysis),
                                use_json_output=self.use_json_output,
                            )
                            completion["success_after_prune"] = success
                            completion["pruned_code"] = pruned_code
                            completion["checker_message_after_prune"] = checker_message
                        except Exception as e:
                            print(e)
                            print(traceback.format_exc())
                            completion["success_after_prune"] = False
                            completion["pruned_code"] = checker_input
                            completion["checker_message_after_prune"] = e.args[0]
                            success = False

                    completions.append(completion)

                instance_log_json["completions"] = completions

                print(f"Checking combined completion")
                checker_input = self.benchmark.combine_llm_outputs(
                    self.benchmark.get_code(instance[0]),
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not llm_output.startswith(
                            "ERROR: Output does not contain at least 1 code block"
                        )
                    ],
                    self.analysis,
                )
                success, checker_message = self.checker.check(
                    checker_input,
                    ("termination" in self.analysis),
                    use_json_output=self.use_json_output,
                )

                instance_log_json["code_with_combined_invariants"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    print("Pruning combined completion")
                    try:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.analysis,
                            use_json_output=self.use_json_output,
                        )
                        success, checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.analysis),
                            use_json_output=self.use_json_output,
                        )
                        instance_log_json["code_after_combine_and_prune"] = pruned_code
                        instance_log_json[
                            "checker_output_after_combine_and_prune"
                        ] = success
                        instance_log_json[
                            "checker_message_after_combine_and_prune"
                        ] = checker_message
                    except Exception as e:
                        print(e)
                        instance_log_json[
                            "checker_output_after_combine_and_prune"
                        ] = False
                        instance_log_json[
                            "code_after_combine_and_prune"
                        ] = checker_input
                        instance_log_json[
                            "checker_message_after_combine_and_prune"
                        ] = e.args[0]
                        success = False

                if success:
                    stats["success"].append(i)
                else:
                    stats["failure"].append(i)
                stats["total"] += 1

                stats["success_rate"] = (
                    len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
                )

                with open(
                    os.path.join(
                        self.log_path,
                        instance[0]
                        .replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
            except (Exception, KeyboardInterrupt) as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                stats["skipped"].append(i)
                with open(
                    os.path.join(
                        self.log_path,
                        instance[0]
                        .replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        stats["success_rate"] = (
            len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
        )
        stats["success_count"] = len(stats["success"])
        stats["failure_count"] = len(stats["failure"])
        stats["skipped_count"] = len(stats["skipped"])

        log_file.write(
            json.dumps(
                {"params": self.arg_params, "logs": log_json, "stats": stats},
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

        return

    def run_classification(self, max_benchmarks=1, start_index=0, ground_truth_file=""):
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        log_json = []
        stats = {"success": [], "failure": [], "partial": [], "skipped": [], "total": 0}

        # create logs dir
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))
        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")

        sliced_benchmarks = self.benchmark.input_file_paths[
            start_index : start_index + max_benchmarks
        ]

        sliced_benchmarks = [
            (instance, {"code": self.benchmark.get_code(instance)})
            for instance in sliced_benchmarks
        ]

        if ground_truth_file == "":
            raise Exception("Ground truth file not provided")

        ground_truth = None
        with open(ground_truth_file, "r", encoding="utf-8") as f:
            ground_truth = json.load(f)
            ground_truth = ground_truth[start_index : start_index + max_benchmarks]

        for i, instance in enumerate(sliced_benchmarks):
            assert instance[0] == ground_truth[i]["file"]
            print(
                f"Classifying benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}"
            )

            instance_log_json = {
                "file": instance[0],
                "benchmark_code": self.benchmark.get_code(instance[0]),
                "ground_truth": ground_truth[i]["label"],
            }

            completions = []
            try:
                llm_outputs, llm_conversation = self.llm.generate_annotation(
                    instance[1],
                    output_full_tree=False,
                    label_only=True,
                )

                completions = []
                for j, llm_output in enumerate(llm_outputs):
                    completion = {}
                    if llm_output is None:
                        completion["success"] = False
                        completion["llm_output"] = "None"
                        completion["error"] = "Output does not contain a label"
                        Logger.log_error(f"Completion {j + 1} does not have a label")
                        completions.append(completion)

                        continue

                    completion["label"] = llm_output
                    completion["success"] = (
                        llm_output == str(instance_log_json["ground_truth"]).lower()
                    )
                    if completion["success"]:
                        Logger.log_success(f"Completion {j + 1} is correct")
                    else:
                        Logger.log_error(f"Completion {j + 1} is incorrect")

                    completions.append(completion)

                instance_log_json["completions"] = completions
                instance_log_json["success"] = sum(
                    [x["success"] for x in completions]
                ) / len(completions)
                instance_log_json["label"] = instance_log_json["success"]

                if instance_log_json["ground_truth"] == False:
                    instance_log_json["label"] = 1 - instance_log_json["label"]

                instance_log_json["llm_conversation"] = llm_conversation

                Logger.log_info(
                    f"Ground truth label: {1 if instance_log_json['ground_truth'] else 0}, Predicted label: {instance_log_json['label']}"
                )

                if instance_log_json["success"] == 1.0:
                    stats["success"].append(i)
                elif instance_log_json["success"] == 0.0:
                    stats["failure"].append(i)
                else:
                    stats["partial"].append(i)

                stats["total"] += 1
                stats["success_rate"] = (
                    len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
                )

                with open(
                    os.path.join(
                        self.log_path,
                        instance[0]
                        .replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )

                log_json.append(instance_log_json)

            except (Exception, KeyboardInterrupt) as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                stats["skipped"].append(i)
                with open(
                    os.path.join(
                        self.log_path,
                        instance[0]
                        .replace(".c", ".json")
                        .replace("../", "")
                        .replace("/", "__"),
                    ),
                    "w",
                    encoding="utf-8",
                ) as f:
                    f.write(
                        json.dumps(
                            {
                                "logs": instance_log_json,
                                "stats": stats,
                            },
                            indent=4,
                            ensure_ascii=False,
                        )
                    )
                log_json.append(instance_log_json)
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        stats["success_rate"] = (
            len(stats["success"]) / stats["total"] if stats["total"] != 0 else 0
        )
        stats["success_count"] = len(stats["success"])
        stats["failure_count"] = len(stats["failure"])
        stats["partial_count"] = len(stats["partial"])
        stats["skipped_count"] = len(stats["skipped"])

        log_file.write(
            json.dumps(
                {"params": self.arg_params, "logs": log_json, "stats": stats},
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

        return

    def run_sequence(self, max_benchmarks=1, start_index=0):
        if self.llm is None or self.benchmark is None or self.checker is None:
            raise Exception("Pipeline not initialized. Call load_config first.")

        if not all([x in ["loop_invariants", "loop_variants"] for x in self.analysis]):
            raise Exception("Unsupported analysis for sequence pipeline")

        log_json = []
        stats = {"success": [], "failure": [], "skipped": [], "total": 0}

        # create logs dir
        self.log_path = datetime.datetime.now().strftime(
            f"../logs/loopy_%Y_%m_%d_%H_%M_%S/"
        )
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))

        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")

        sliced_benchmarks = self.benchmark.input_file_paths[
            start_index : start_index + max_benchmarks
        ]

        for benchmark_index, benchmark_file in enumerate(sliced_benchmarks):
            Logger.log_info(
                f"Running benchmark: {start_index + benchmark_index + 1}/{len(sliced_benchmarks)}"
            )

            instance_log_json = {
                "file": benchmark_file,
                "benchmark_code": self.benchmark.get_code(benchmark_file),
                "success": False,
                "log": [],
            }
            annotations = {}
            pipeline_outputs = []

            for step_index, step in enumerate(self.steps):
                try:
                    if type(step) == dict:
                        # This step just makes an LLM call and stores the output code block
                        prompt, annotation_type = (
                            step["prompt"],
                            step["annotation_type"],
                        )
                        step_log_json = {
                            "step": "Prompting LLM",
                            "generating_annotation": annotation_type,
                            "success": True,
                        }
                        Logger.log_info(
                            f"[Step {step_index + 1}] Prompting {self.model} for {annotation_type}"
                        )

                        generated_code_blocks = None
                        llm_output_text = None

                        extraction_filter = None
                        if annotation_type == "loop_invariants":
                            extraction_filter = self.checker.is_invariant
                        elif annotation_type == "loop_variants":
                            extraction_filter = self.checker.is_variant
                        else:
                            raise Exception("Unsupported annotation type")

                        # Make the LLM query and get the code blocks, and the LLM output
                        (
                            generated_code_blocks,
                            llm_output_text,
                        ) = self.llm.generate_annotation(
                            input={"code": self.benchmark.get_code(benchmark_file)},
                            prompt=prompt,
                            extraction_filter=extraction_filter,
                        )

                        step_log_json["llm_chat"] = llm_output_text
                        step_log_json["output"] = generated_code_blocks
                        annotations[annotation_type] = generated_code_blocks

                        pipeline_outputs.append(step_log_json)

                    elif step == "check_individual_completion":
                        step_log_json = {
                            "step": "Checking individual completion",
                            "solver_calls": 0,
                            "completions": [],
                            "success": False,
                        }
                        Logger.log_info(
                            f"[Step {step_index + 1}] Checking individual completion"
                        )
                        if annotations == {}:  # No annotations generated
                            raise Exception(
                                "No annotations to check for this benchmark"
                            )

                        elif (
                            "loop_invariants" not in annotations
                            and "loop_variants" in annotations
                        ):
                            raise Exception(
                                "No loop invariants generated for this benchmark"
                            )

                        elif (
                            "loop_variants" in annotations
                            and "loop_invariants" in annotations
                            and type(annotations["loop_invariants"]) != str
                        ):
                            # Houdini loop was not run maybe?
                            raise Exception(
                                "More than 1 loop inductive invariant set exists for this benchmark"
                            )

                        elif (
                            "loop_variants" not in annotations
                            or len(annotations["loop_variants"]) == 0
                        ):
                            completions = []
                            for ann_index, llm_output in enumerate(
                                annotations["loop_invariants"]
                            ):
                                Logger.log_info(
                                    f"Checking completion {ann_index + 1}/{len(annotations['loop_invariants'])} for benchmark: {start_index + benchmark_index + 1}/{len(sliced_benchmarks)}"
                                )

                                completion = {"num_solver_calls": 0, "success": False}

                                # If the completion does not have a code block,
                                # mark it as a failure and continue
                                if len(llm_output) == 2 and llm_output[0] == (
                                    "ERROR: Output does not contain at least 1 code block"
                                ):
                                    completion["success"] = False
                                    completion["num_solver_calls"] = 0
                                    completion["llm_output"] = llm_output[1]
                                    completion[
                                        "error"
                                    ] = "Output does not contain at least 1 code block"
                                    completions.append(completion)
                                    continue

                                # Add only the loop invariants to the code and check
                                checker_input_with_invariants = self.benchmark.combine_llm_outputs(
                                    self.benchmark.get_code(benchmark_file),
                                    [
                                        llm_output
                                        if not (
                                            len(llm_output) == 2
                                            and llm_output[0]
                                            == "ERROR: Output does not contain at least 1 code block"
                                        )
                                        else ""
                                    ],
                                    "one_loop_one_method",
                                )
                                completion["invariants"] = llm_output
                                success, checker_message = self.checker.check(
                                    checker_input_with_invariants,
                                    False,
                                    use_json_output=self.use_json_output,
                                )

                                completion["num_solver_calls"] += 1
                                completion["checker_output_for_invariants"] = success
                                completion[
                                    "checker_message_for_invariants"
                                ] = checker_message
                                completion["success"] = success
                                if success:
                                    step_log_json["success"] = True
                                    Logger.log_success(
                                        f"Completion {ann_index + 1} is correct"
                                    )
                                else:
                                    Logger.log_error(
                                        f"Completion {ann_index + 1} is incorrect"
                                    )

                                completions.append(completion)

                            step_log_json["completions"] = completions
                            step_log_json["solver_calls"] = sum(
                                [x["num_solver_calls"] for x in completions]
                            )
                            pipeline_outputs.append(step_log_json)

                        elif (
                            "loop_variants" in annotations
                            and len(annotations["loop_variants"]) > 0
                            and "loop_invariants" in annotations
                            and type(annotations["loop_invariants"]) == str
                        ):
                            checker_inputs_with_variants = self.benchmark.combine_llm_outputs(
                                self.benchmark.get_code(benchmark_file),
                                (
                                    annotations["loop_invariants"],
                                    [
                                        llm_output
                                        for llm_output in annotations["loop_variants"]
                                        if not (
                                            len(llm_output) == 2
                                            and llm_output[0]
                                            == "ERROR: Output does not contain at least 1 code block"
                                        )
                                    ],
                                ),
                                "termination_one_loop_one_method",
                            )

                            candidates = []

                            for c_index, checker_input in enumerate(
                                checker_inputs_with_variants
                            ):
                                Logger.log_info(
                                    f"Checking completion {c_index + 1}/{len(checker_inputs_with_variants)} for benchmark: {start_index + benchmark_index + 1}/{len(sliced_benchmarks)}"
                                )
                                success, checker_message = self.checker.check(
                                    checker_input,
                                    True,
                                    use_json_output=self.use_json_output,
                                )
                                combined_candidate_with_variant = {}
                                combined_candidate_with_variant[
                                    "candidate_with_combined_invariants_and_variant"
                                ] = checker_input
                                combined_candidate_with_variant[
                                    "checker_output"
                                ] = success
                                combined_candidate_with_variant[
                                    "checker_message"
                                ] = checker_message

                                candidates.append(combined_candidate_with_variant)

                                step_log_json["solver_calls"] += 1
                                if success:
                                    step_log_json["success"] = True
                                    Logger.log_success(
                                        f"Completion {c_index + 1} is correct"
                                    )
                                else:
                                    Logger.log_error(
                                        f"Completion {c_index + 1} is incorrect"
                                    )

                            step_log_json["completions"] = candidates
                            pipeline_outputs.append(step_log_json)

                        else:
                            print(annotations)
                            raise Exception("Unsupported annotation combination ^")

                    elif step == "houdini_for_individual_completion":
                        step_log_json = {
                            "step": "Houdini for individual completion",
                            "success": False,
                        }
                        Logger.log_info(
                            f"[Step {step_index + 1}] Houdini for individual completions"
                        )

                        if (
                            "loop_invariants" not in annotations
                            or len(annotations["loop_invariants"]) == 0
                        ):
                            raise Exception(
                                "No loop invariants found for this benchmark"
                            )

                        completions = []
                        for ann_index, llm_output in enumerate(
                            annotations["loop_invariants"]
                        ):
                            Logger.log_info(
                                f"Checking completion {ann_index + 1}/{len(annotations['loop_invariants'])} for benchmark: {start_index + benchmark_index + 1}/{len(sliced_benchmarks)}"
                            )

                            completion = {"num_solver_calls": 0, "success": False}

                            # If the completion does not have a code block,
                            # mark it as a failure and continue
                            if len(llm_output) == 2 and llm_output[0] == (
                                "ERROR: Output does not contain at least 1 code block"
                            ):
                                completion["success"] = False
                                completion["num_solver_calls"] = 0
                                completion["llm_output"] = llm_output[1]
                                completion[
                                    "error"
                                ] = "Output does not contain at least 1 code block"
                                completions.append(completion)
                                continue

                            # Add only the loop invariants to the code and check
                            checker_input_with_invariants = self.benchmark.combine_llm_outputs(
                                self.benchmark.get_code(benchmark_file),
                                [
                                    llm_output
                                    if not (
                                        len(llm_output) == 2
                                        and llm_output[0]
                                        == "ERROR: Output does not contain at least 1 code block"
                                    )
                                    else ""
                                ],
                                "one_loop_one_method",
                            )
                            completion["invariants"] = llm_output
                            (
                                success,
                                pruned_code,
                                num_frama_c_calls,
                            ) = self.checker.prune_annotations_and_check(
                                checker_input_with_invariants,
                                "one_loop_one_method",
                                use_json_output=self.use_json_output,
                            )

                            completion["num_solver_calls"] += num_frama_c_calls
                            completion["code_after_prune"] = pruned_code
                            completion["checker_output_after_prune"] = success

                            if success:
                                step_log_json["success"] = True
                                Logger.log_success(
                                    f"Completion {ann_index + 1} is correct"
                                )
                            else:
                                Logger.log_error(
                                    f"Completion {ann_index + 1} is incorrect"
                                )

                            completions.append(completion)

                        step_log_json["completions"] = completions
                        pipeline_outputs.append(step_log_json)

                    elif step == "houdini_for_combined_completion":
                        step_log_json = {
                            "step": "Houdini for combined completion",
                            "solver_calls": 0,
                            "success": False,
                        }
                        Logger.log_info(
                            f"[Step {step_index + 1}] Houdini for combined completion"
                        )

                        if (
                            "loop_invariants" not in annotations
                            or len(annotations["loop_invariants"]) == 0
                        ):
                            raise Exception(
                                "No loop invariants found for this benchmark"
                            )

                        code_with_combined_invariants = self.benchmark.combine_llm_outputs(
                            self.benchmark.get_code(benchmark_file),
                            [
                                llm_output
                                for llm_output in annotations["loop_invariants"]
                                if not (
                                    len(llm_output) == 2
                                    and llm_output[0]
                                    == "ERROR: Output does not contain at least 1 code block"
                                )
                            ],
                            "one_loop_one_method",
                        )
                        (
                            success,
                            pruned_code,
                            num_frama_c_calls,
                        ) = self.checker.prune_annotations_and_check(
                            code_with_combined_invariants,
                            "one_loop_one_method",
                            use_json_output=self.use_json_output,
                        )

                        inductive_invariants = self.benchmark.extract_loop_invariants(
                            pruned_code
                        )
                        annotations["loop_invariants"] = inductive_invariants

                        step_log_json["solver_calls"] += num_frama_c_calls
                        step_log_json["code_with_combined_invariants"] = pruned_code
                        step_log_json["checker_output"] = success

                        if success:
                            step_log_json["success"] = True
                            Logger.log_success(
                                f"Houdini for combined completion successful"
                            )
                        else:
                            Logger.log_error(
                                f"Houdini for combined completion unsuccessful"
                            )

                        pipeline_outputs.append(step_log_json)

                    else:
                        raise Exception("Unsupported step")

                except Exception as e:
                    if isinstance(e, KeyboardInterrupt):
                        step_log_json["error"] = str(e)
                        instance_log_json["log"].append(step_log_json)
                        stats["skipped"].append(benchmark_file)
                        break
                    Logger.log_error(e)
                    step_log_json["error"] = str(e)
                    instance_log_json["log"].append(step_log_json)
                    stats["skipped"].append(benchmark_file)
                    continue

            instance_log_json["log"] = pipeline_outputs
            instance_log_json["success"] = pipeline_outputs[-1]["success"]
            if instance_log_json["success"]:
                stats["success"].append(benchmark_file)
            else:
                stats["failure"].append(benchmark_file)

            stats["total"] += 1
            stats["success_count"] = len(stats["success"])
            stats["failure_count"] = len(stats["failure"])
            stats["success_rate"] = (
                stats["success_count"] / stats["total"] if stats["total"] != 0 else 0
            )

            log_json.append(instance_log_json)

            with open(
                os.path.join(
                    self.log_path,
                    benchmark_file.replace(".c", ".json")
                    .replace("../", "")
                    .replace("/", "__"),
                ),
                "w",
                encoding="utf-8",
            ) as f:
                f.write(
                    json.dumps(
                        {
                            "logs": instance_log_json,
                            "stats": stats,
                        },
                        indent=4,
                        ensure_ascii=False,
                    )
                )

        log_file.write(
            json.dumps(
                {"params": self.arg_params, "logs": log_json, "stats": stats},
                indent=4,
                ensure_ascii=False,
            )
        )
        log_file.close()

        return

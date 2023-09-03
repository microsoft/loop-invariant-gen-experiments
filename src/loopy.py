import json
import os
import random
import re
import traceback
from copy import deepcopy

import yaml

from benchmark import Benchmark
from checker import Checker
from loopy_llm import LLM, PromptConfig
from llm_utils import Logger
from process_results import run_parallel, prune_wrapper, shuffle


def combine_and_prune_with_k(
    benchmark,
    benchmark2,
    n,
    k,
    shuffle_times=10,
    max_cores=10,
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
                f"[Batch {m+1}/{max_m}]: Combine and Prune with k = {pass_k_prune / len(results)} for k={k}, \
                    {len(candidates_batch)} parallel benchmarks, File: {benchmark['file']}"
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
        nudge: bool = True,
        features: str = "one_loop_one_method",
        arg_params: dict = None,
        ground_truth: bool = False,
        use_json_output: bool = False,
    ):
        self.benchmark = benchmark
        self.checker = checker
        self.model = model
        self.debug = debug
        self.log_path = log_path

        self.num_repair_retries = num_repair_retries
        self.nudge = nudge
        self.repair_errors_input = repair_errors_input
        self.repair_errors_input_2 = repair_errors_input_2
        self.repair_from_k = repair_from_k
        self.system_message = ""
        self.features = features
        self.arg_params = arg_params
        self.ground_truth = ground_truth
        self.use_json_output = use_json_output

    def load_config(self, config_file):
        config = yaml.load(open(config_file, "r"), Loader=yaml.FullLoader)

        prompt_configs = []
        if "prompts" in config:
            prompt_template_dir = (
                None
                if "prompt_template_dir" not in config
                else config["prompt_template_dir"]
            )

            for prompt_config in config["prompts"]:
                prompt_configs.append(
                    PromptConfig(dir=prompt_template_dir).from_file(prompt_config)
                )

        healing_prompt_configs = []
        if "healing_prompts" in config:
            healing_template_dir = (
                None
                if "healing_template_dir" not in config
                else config["healing_template_dir"]
            )

            for healing_prompt_config in config["healing_prompts"]:
                healing_prompt_configs.append(
                    PromptConfig(dir=healing_template_dir).from_file(
                        healing_prompt_config
                    )
                )

        if "system_message_file" in config:
            self.system_message_file = config["system_message_file"]
            self.system_message = open(self.system_message_file, "r").read()

        nudge_config = None
        if "nudge_prompts" in config:
            self.nudge_prompts_file = config["nudge_prompts"]
            nudge_config = PromptConfig(dir=".").from_file(self.nudge_prompts_file)

        self.llm = LLM(
            self.system_message,
            prompt_configs,
            healing_prompt_configs,
            self.model,
            self.debug,
            nudge_config,
        )

        if "llm_input_file_path" not in config:
            config["llm_input_file_path"] = ""

        if "llm_input_dir" not in config:
            config["llm_input_dir"] = "llm_input"
        if self.benchmark is None:
            self.benchmark = Benchmark(
                config["llm_input_dir"],
                config["llm_input_file_path"],
                self.features,
            )
        else:
            self.benchmark.llm_input_path = config["llm_input_dir"]
            self.benchmark.llm_input_file = config["llm_input_file_path"]
            self.benchmark.features = self.features
        self.benchmark.check_input()

        if "healing_retries" in config:
            self.num_repair_retries = config["healing_retries"]

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

        for i, instance in enumerate(sliced_benchmarks):
            print(f"Running benchmark: {start_index + i + 1}/{len(sliced_benchmarks)}")

            instance_log_json = {
                "file": instance,
                "benchmark_code": self.benchmark.get_code(instance),
            }
            try:
                llm_outputs = None
                conversations = None
                if self.ground_truth:
                    llm_outputs = ["loop invariant \\true;"]
                else:
                    llm_outputs, conversations = self.llm.run(
                        {"code": self.benchmark.get_code(instance)},
                        output_full_tree=True,
                    )

                completions = []
                if not self.ground_truth:
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
                            self.benchmark.get_code(instance),
                            [llm_output if not llm_output.startswith("ERROR") else ""],
                            self.features,
                        )
                        completion["invariants"] = llm_output
                        completion["code_with_invariants"] = checker_input
                        success, checker_message = self.checker.check(
                            checker_input,
                            ("termination" in self.features),
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
                                    self.features,
                                    use_json_output=self.use_json_output,
                                )
                                success, checker_message = self.checker.check(
                                    pruned_code,
                                    ("termination" in self.features),
                                    use_json_output=self.use_json_output,
                                )
                                completion["success_after_prune"] = success
                                completion["pruned_code"] = pruned_code
                                completion[
                                    "checker_message_after_prune"
                                ] = checker_message
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
                    self.benchmark.get_code(instance),
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not llm_output.startswith(
                            "ERROR: Output does not contain at least 1 code block"
                        )
                    ],
                    self.features,
                )
                success, checker_message = self.checker.check(
                    checker_input,
                    ("termination" in self.features),
                    use_json_output=self.use_json_output,
                )

                if not self.ground_truth:
                    instance_log_json[
                        "llm_conversation"
                    ] = conversations.get_full_tree()
                else:
                    instance_log_json[
                        "llm_conversation"
                    ] = "This was a ground truth experiment."
                instance_log_json["invariants"] = llm_outputs
                instance_log_json["code_with_combined_invariants"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    print("Pruning combined completion")
                    try:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.features,
                            use_json_output=self.use_json_output,
                        )
                        success, checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.features),
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

                if not success and self.nudge:
                    nudge_outputs, nudge_conversation = self.llm.nudge(
                        input_tree=deepcopy(conversations),
                        output_full_tree=True,
                    )
                    nudge_checker_input = self.benchmark.combine_llm_outputs(
                        self.benchmark.get_code(instance),
                        nudge_outputs + llm_outputs,
                        self.features,
                    )
                    checker_input = nudge_checker_input
                    success, nudge_checker_message = self.checker.check(
                        nudge_checker_input,
                        ("termination" in self.features),
                        use_json_output=self.use_json_output,
                    )

                    instance_log_json[
                        "nudge_conversation"
                    ] = nudge_conversation.get_full_tree()
                    instance_log_json["invariants_after_nudge"] = nudge_outputs
                    instance_log_json["checker_input_after_nudge"] = nudge_checker_input
                    instance_log_json["checker_output_after_nudge"] = success
                    instance_log_json[
                        "checker_message_after_nudge"
                    ] = nudge_checker_message

                    if not success:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.features,
                            use_json_output=self.use_json_output,
                        )
                        success, checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.features),
                            use_json_output=self.use_json_output,
                        )

                        instance_log_json["code_after_nudge_and_prune"] = pruned_code
                        instance_log_json[
                            "checker_output_after_nudge_and_prune"
                        ] = success
                        instance_log_json[
                            "checker_message_after_nudge_and_prune"
                        ] = checker_message

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
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                stats["skipped"].append(i)
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
            prune_and_check_with_k, failing_invariants = combine_and_prune_with_k(
                instance,
                error_logs_2[i],
                15,
                self.repair_from_k,
                combine_llm_output_lambda=self.benchmark.combine_llm_outputs,
                features=self.features,
            )
            if prune_and_check_with_k > 0.0:
                print(
                    "Skipping successful benchmark: {i}/{n}".format(
                        i=i, n=len(error_logs)
                    )
                )
                stats["success"].append(i)
                stats["total"] += 1
                continue

            print("Healing benchmark: {i}/{n}".format(i=i, n=len(error_logs)))
            instance_log_json = {"file": instance["file"]}
            try:
                success = False
                num_retries = 0
                instance_log_json["healing_conversations"] = []

                failed_checker_input = self.benchmark.combine_llm_outputs(
                    instance["benchmark_code"],
                    failing_invariants,
                    self.features,
                )
                success, checker_error_message = self.checker.check(
                    failed_checker_input,
                    ("termination" in self.features),
                    use_json_output=self.use_json_output,
                )

                instance_log_json["code_with_failing_invariants"] = failed_checker_input
                instance_log_json["checker_fail_error_message"] = checker_error_message

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
                        self.features,
                    )
                    success, checker_message = self.checker.check(
                        checker_input,
                        ("termination" in self.features),
                        use_json_output=self.use_json_output,
                    )

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
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input,
                            self.features,
                            use_json_output=self.use_json_output,
                        )
                        success, prune_checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.features),
                            use_json_output=self.use_json_output,
                        )
                        healing_json["code_after_combine_and_prune"] = pruned_code
                        healing_json["checker_output_after_combine_and_prune"] = success
                        healing_json[
                            "checker_message_after_combine_and_prune"
                        ] = prune_checker_message

                        failed_checker_input = checker_input
                        checker_error_message = checker_message

                    instance_log_json["healing_conversations"].append(healing_json)
                    num_retries += 1

                if not success:
                    success, pruned_code = self.checker.prune_annotations_and_check(
                        checker_input,
                        self.features,
                        use_json_output=self.use_json_output,
                    )
                    success, prune_checker_message = self.checker.check(
                        pruned_code,
                        ("termination" in self.features),
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
            # if not any(
            #     [
            #         (c["checker_message"] == "No invariants found.")
            #         for c in instance["completions"]
            #     ]
            # ):
            #     if "checker_output" not in instance.keys():
            #         stats["skipped"].append(i)
            #         log_json.append(instance)
            #     else:
            #         success = (
            #             instance["checker_output"]
            #             if "checker_output_after_combine_and_prune"
            #             not in instance.keys()
            #             else instance["checker_output_after_combine_and_prune"]
            #         )
            #         log_json.append(instance)
            #         if success:
            #             stats["success"].append(i)
            #         else:
            #             stats["failure"].append(i)
            #         stats["total"] += 1
            #         print("Skipping benchmark: {i}/{n}".format(i=start_index + i + 1, n=total))
            #     continue

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
                        self.features,
                    )
                    completion["invariants"] = llm_output
                    completion["code_with_invariants"] = checker_input
                    success, checker_message = self.checker.check(
                        checker_input,
                        ("termination" in self.features),
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
                                self.features,
                                use_json_output=self.use_json_output,
                            )
                            success, checker_message = self.checker.check(
                                pruned_code,
                                ("termination" in self.features),
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
                    self.features,
                )
                success, checker_message = self.checker.check(
                    checker_input,
                    ("termination" in self.features),
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
                            self.features,
                            use_json_output=self.use_json_output,
                        )
                        success, checker_message = self.checker.check(
                            pruned_code,
                            ("termination" in self.features),
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

                # if not success and "invariants_after_nudge" in instance:
                #     checker_input_with_invariants_after_nudge = (
                #         self.benchmark.combine_llm_outputs(
                #             checker_input_without_invariants,
                #             instance["invariants"] + instance["invariants_after_nudge"],
                #             self.mode,
                #         )
                #     )
                #     instance_log_json[
                #         "checker_input_after_nudge"
                #     ] = checker_input_with_invariants_after_nudge
                #     success, checker_message = self.checker.check(
                #         checker_input_with_invariants_after_nudge, self.mode, use_json_output=self.use_json_output
                #     )
                #     instance_log_json["checker_output_after_nudge"] = success
                #     instance_log_json["checker_message_after_nudge"] = checker_message

                #     if not success:
                #         success, pruned_code = self.checker.prune_annotations_and_check(
                #             checker_input_with_invariants_after_nudge, self.mode, use_json_output=self.use_json_output
                #         )
                #         success, prune_checker_message = self.checker.check(
                #             pruned_code, self.mode, use_json_output=self.use_json_output
                #         )
                #         instance_log_json["code_after_nudge_and_prune"] = pruned_code
                #         instance_log_json[
                #             "checker_output_after_nudge_and_prune"
                #         ] = success
                #         instance_log_json[
                #             "checker_message_after_nudge_and_prune"
                #         ] = prune_checker_message

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

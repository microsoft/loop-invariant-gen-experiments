from copy import deepcopy
import json
import os
import traceback

import yaml

from benchmark import Benchmark
from checker import Checker
from loopy_llm import LLM, PromptConfig


class LoopyPipeline:
    # TODO: why is the model gpt-3.5?

    def __init__(
        self,
        benchmark: Benchmark = None,
        checker: Checker = Checker("boogie"),
        model: str = "gpt-3.5-turbo",
        debug: bool = False,
        log_path: str = None,
        num_healing_retries: int = 5,
        heal_errors: bool = False,
        heal_errors_input: str = "",
        nudge: bool = True,
        mode: str = "invariant",
        multiple_loops: bool = False,
    ):
        self.benchmark = benchmark
        self.checker = checker
        self.model = model
        self.debug = debug
        self.log_path = log_path

        self.num_healing_retries = num_healing_retries
        self.heal_errors = heal_errors
        self.nudge = nudge
        self.heal_errors_input = heal_errors_input
        self.system_message = None
        self.mode = mode
        self.multiple_loops = multiple_loops

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
        if "checker_input_dir" not in config:
            config["checker_input_dir"] = "checker_input"
        if self.benchmark is None:
            self.benchmark = Benchmark(
                config["llm_input_dir"],
                config["checker_input_dir"],
                config["llm_input_file_path"],
                self.multiple_loops
            )
        else:
            self.benchmark.llm_input_path = config["llm_input_dir"]
            self.benchmark.checker_input_path = config["checker_input_dir"]
            self.benchmark.llm_input_file = config["llm_input_file_path"]
            self.benchmark.multiple_loops = self.multiple_loops
        self.benchmark.load_instances()

        if "healing_retries" in config:
            self.num_healing_retries = config["healing_retries"]

        return self

    def run(self, max_benchmarks=1, start_index=0, recheck_logfile=None):
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        if self.heal_errors:
            return self.heal(max_benchmarks, start_index)

        log_json = []
        stats = {"success": [], "failure": [], "total": 0}
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))
        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")
        recheck_logs = None
        total_benchmarks = len(
            self.benchmark.instances[start_index : start_index + max_benchmarks]
        )
        for i, instance in enumerate(
            self.benchmark.instances[start_index : start_index + max_benchmarks]
        ):
            if recheck_logfile is not None and os.path.exists(recheck_logfile):
                with open(recheck_logfile, "r", encoding="utf-8") as f:
                    recheck_logs = json.load(f)

            print(f"Running benchmark: {start_index+i+1}/{total_benchmarks}")
            instance_log_json = {"file": instance.llm_input_path}
            try:
                if recheck_logs is None:
                    llm_outputs, conversations = self.llm.run(
                        {"code": instance.llm_input}, output_full_tree=True
                    )
                else:
                    llm_outputs, conversations = (
                        recheck_logs["logs"][start_index + i]["final_code_outputs"],
                        recheck_logs["logs"][start_index + i]["llm_conversation"],
                    )

                checker_input = self.benchmark.combine_llm_outputs(
                    instance.checker_input
                    if not recheck_logs
                    else recheck_logs["logs"][start_index + i][
                        "checker_input_without_invariants"
                    ],
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not llm_output.startswith("ERROR")
                    ],
                    self.mode,
                )
                success, checker_message = self.checker.check(checker_input, self.mode)

                instance_log_json["llm_conversation"] = conversations.get_full_tree()
                instance_log_json["invariants"] = llm_outputs
                instance_log_json["checker_input_without_invariants"] = (
                    instance.checker_input
                    if not recheck_logs
                    else recheck_logs["logs"][start_index + i][
                        "checker_input_without_invariants"
                    ]
                )
                instance_log_json["checker_input_with_invariants"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    success, pruned_code = self.checker.prune_annotations_and_check(
                        checker_input, self.mode
                    )
                    success, checker_message = self.checker.check(pruned_code, self.mode)

                    instance_log_json["code_after_prune"] = pruned_code
                    instance_log_json["checker_output_after_prune"] = success
                    instance_log_json["checker_message_after_prune"] = checker_message

                if not success and self.nudge:
                    nudge_outputs, nudge_conversation = self.llm.nudge(
                        input_tree=deepcopy(conversations),
                        output_full_tree=True,
                    )
                    nudge_checker_input = self.benchmark.combine_llm_outputs(
                        instance.checker_input, nudge_outputs + llm_outputs, self.mode
                    )
                    checker_input = nudge_checker_input
                    success, nudge_checker_message = self.checker.check(
                        nudge_checker_input, self.mode
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
                            checker_input, self.mode
                        )
                        success, checker_message = self.checker.check(pruned_code, self.mode)

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

                with open(
                    os.path.join(
                        self.log_path,
                        instance.llm_input_path.replace(".c", ".json")
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
                with open(
                    os.path.join(
                        self.log_path,
                        instance.llm_input_path.replace(".c", ".json")
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
                stats["failure"].append(i)
                stats["total"] += 1
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        if stats["total"] != 0:
            stats["success_rate"] = len(stats["success"]) / stats["total"]
        else:
            stats["success_rate"] = 0

        log_file.write(
            json.dumps({"logs": log_json, "stats": stats}, indent=4, ensure_ascii=False)
        )
        log_file.close()

        return

    def heal(self, max_benchmarks=1, start_index=0):
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        error_logs = None
        with open(self.heal_errors_input, "r", encoding="utf-8") as f:
            error_logs = json.load(f)

        error_logs = error_logs["logs"]

        log_json = []
        stats = {"success": [], "failure": [], "total": 0}
        if not os.path.exists(os.path.dirname(self.log_path)):
            os.makedirs(os.path.dirname(self.log_path))
        log_file = open(self.log_path + "final.json", "w", encoding="utf-8")
        for i, instance in enumerate(
            error_logs[start_index : start_index + max_benchmarks]
        ):
            if "checker_output" in instance.keys() and (
                instance["checker_output"] or instance["checker_output_after_prune"]
            ):
                stats["success"].append(i)
                stats["total"] += 1
                print(
                    "Skipping successful benchmark: {i}/{n}".format(
                        i=i, n=len(error_logs)
                    )
                )
                continue
            if "checker_output_after_nudge" in instance.keys() and (
                instance["checker_output_after_nudge"]
                or instance["checker_output_after_nudge_and_prune"]
            ):
                stats["success"].append(i)
                stats["total"] += 1
                print(
                    "Skipping successful benchmark: {i}/{n}".format(
                        i=i, n=len(error_logs)
                    )
                )
                continue

            print("Healing benchmark: {i}/{n}".format(i=i, n=len(error_logs)))
            instance_log_json = {"file": instance["file"]}
            try:
                success = False
                num_retries = 0
                instance_log_json["healing_conversations"] = []

                failed_checker_input = None
                checker_error_message = None
                if "code_after_nudge_and_prune" in instance.keys():
                    failed_checker_input = instance["code_after_nudge_and_prune"]
                    checker_error_message = instance["checker_message_after_nudge_and_prune"]
                elif "code_after_prune" in instance.keys():
                    failed_checker_input = instance["code_after_prune"]
                    checker_error_message = instance["checker_message_after_prune"]
                else:
                    # This benchmark was not run previously. So we will skip it.
                    continue

                while not success and num_retries < self.num_healing_retries:
                    healing_json = {}
                    inductive_invs = "\n".join(
                        [
                            x
                            for x in checker_error_message.splitlines()
                            if not "Post-condition" in x
                        ]
                    )
                    analysis = (
                        "the invariants were not inductive"
                        if len(inductive_invs) == 0
                        else "the following subset of the invariants are inductive but they are not strong enough to prove the post-condition:\n"
                        + inductive_invs
                    )
                    llm_outputs, conversations = self.llm.heal(
                        input={
                            "code": failed_checker_input,
                            "error": checker_error_message,
                            "analysis": analysis,
                        },
                        output_full_tree=True,
                    )

                    checker_input = self.benchmark.combine_llm_outputs(
                        instance["checker_input_without_invariants"], llm_outputs, self.mode
                    )
                    success, checker_message = self.checker.check(checker_input, self.mode)

                    healing_json["conversation"] = conversations.get_full_tree()
                    healing_json["invariants"] = llm_outputs
                    healing_json["checker_input_without_invariants"] = instance[
                        "checker_input_without_invariants"
                    ]
                    healing_json["checker_input_with_old_invariants"] = instance[
                        "checker_input_with_invariants"
                    ]
                    healing_json["input_error_message"] = instance["checker_message"]
                    healing_json["checker_input_with_new_invariants"] = checker_input
                    healing_json["checker_output"] = success
                    healing_json["checker_message"] = checker_message

                    if not success:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input, self.mode
                        )
                        success, prune_checker_message = self.checker.check(pruned_code, self.mode)
                        healing_json["code_after_prune"] = pruned_code
                        healing_json["checker_output_after_prune"] = success
                        healing_json[
                            "checker_message_after_prune"
                        ] = prune_checker_message

                        failed_checker_input = checker_input
                        checker_error_message = checker_message

                    if not success and self.nudge:
                        nudge_outputs, nudge_conversation = self.llm.nudge(
                            input_tree=deepcopy(conversations),
                            output_full_tree=True,
                        )
                        nudge_checker_input = self.benchmark.combine_llm_outputs(
                            instance["checker_input_without_invariants"], nudge_outputs + llm_outputs, self.mode
                        )
                        checker_input = nudge_checker_input
                        success, nudge_checker_message = self.checker.check(
                            nudge_checker_input, self.mode
                        )

                        instance_log_json[
                            "nudge_conversation"
                        ] = nudge_conversation.get_full_tree()
                        instance_log_json["invariants_after_nudge"] = nudge_outputs
                        instance_log_json[
                            "checker_input_after_nudge"
                        ] = nudge_checker_input
                        instance_log_json["checker_output_after_nudge"] = success
                        instance_log_json[
                            "checker_message_after_nudge"
                        ] = nudge_checker_message

                        if not success:
                            (
                                success,
                                pruned_code,
                            ) = self.checker.prune_annotations_and_check(checker_input, self.mode)
                            success, checker_message = self.checker.check(pruned_code, self.mode)

                            instance_log_json[
                                "code_after_nudge_and_prune"
                            ] = pruned_code
                            instance_log_json[
                                "checker_output_after_nudge_and_prune"
                            ] = success
                            instance_log_json[
                                "checker_message_after_nudge_and_prune"
                            ] = checker_message

                            failed_checker_input = checker_input
                            checker_error_message = checker_message

                    instance_log_json["healing_conversations"].append(healing_json)
                    num_retries += 1

                if success:
                    stats["success"].append(i)
                else:
                    stats["failure"].append(i)
                stats["total"] += 1
                with open(
                    os.path.join(
                        self.log_path,
                        instance["file"].replace("../", "").replace("/", "__"),
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

        if stats["total"] != 0:
            stats["success_rate"] = len(stats["success"]) / stats["total"]
        else:
            stats["success_rate"] = 0

        log_file.write(
            json.dumps(
                {
                    "heal_input": self.heal_errors_input,
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
        with open(input_log_path, "r", encoding="utf-8") as f:
            existing_log_json = json.load(f)

        log_json = []

        stats = {"success": [], "failure": [], "total": 0}
        log_file = open(output_log_path, "w", encoding="utf-8")
        benchmark_subset = existing_log_json["logs"][
            start_index : start_index + max_benchmarks
        ]
        total = len(benchmark_subset)
        for i, instance in enumerate(benchmark_subset):
            print("Rechecking benchmark: {i}/{n}".format(i=i, n=total))
            instance_log_json = deepcopy(instance)
            try:
                success = False
                raw_benchmark = ""
                with open(instance["file"], "r", encoding="utf-8") as f:
                    raw_benchmark = f.read()
                checker_input_without_invariants = (
                    self.benchmark.raw_input_to_checker_input(raw_benchmark)
                )
                instance_log_json[
                    "checker_input_without_invariants"
                ] = checker_input_without_invariants
                checker_input_with_invariants = self.benchmark.combine_llm_outputs(
                    checker_input_without_invariants, instance["invariants"], self.mode
                )
                instance_log_json[
                    "checker_input_with_invariants"
                ] = checker_input_with_invariants
                success, checker_message = self.checker.check(
                    checker_input_with_invariants, self.mode
                )
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    success, pruned_code = self.checker.prune_annotations_and_check(
                        checker_input_with_invariants, self.mode
                    )
                    success, prune_checker_message = self.checker.check(pruned_code, self.mode)
                    instance_log_json["code_after_prune"] = pruned_code
                    instance_log_json["checker_output_after_prune"] = success
                    instance_log_json[
                        "checker_message_after_prune"
                    ] = prune_checker_message

                if not success and "invariants_after_nudge" in instance:
                    checker_input_with_invariants_after_nudge = (
                        self.benchmark.combine_llm_outputs(
                            checker_input_without_invariants,
                            instance["invariants"] + instance["invariants_after_nudge"],
                            self.mode,
                        )
                    )
                    instance_log_json[
                        "checker_input_after_nudge"
                    ] = checker_input_with_invariants_after_nudge
                    success, checker_message = self.checker.check(
                        checker_input_with_invariants_after_nudge, self.mode
                    )
                    instance_log_json["checker_output_after_nudge"] = success
                    instance_log_json["checker_message_after_nudge"] = checker_message

                    if not success:
                        success, pruned_code = self.checker.prune_annotations_and_check(
                            checker_input_with_invariants_after_nudge, self.mode
                        )
                        success, prune_checker_message = self.checker.check(pruned_code, self.mode)
                        instance_log_json["code_after_nudge_and_prune"] = pruned_code
                        instance_log_json[
                            "checker_output_after_nudge_and_prune"
                        ] = success
                        instance_log_json[
                            "checker_message_after_nudge_and_prune"
                        ] = prune_checker_message

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
                stats["failure"].append(i)
                stats["total"] += 1
                if isinstance(e, KeyboardInterrupt):
                    break
                else:
                    continue

        if stats["total"] != 0:
            stats["success_rate"] = len(stats["success"]) / stats["total"]
        else:
            stats["success_rate"] = 0

        log_file.write(
            json.dumps({"logs": log_json, "stats": stats}, indent=4, ensure_ascii=False)
        )
        log_file.close()

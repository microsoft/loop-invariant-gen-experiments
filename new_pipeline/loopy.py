import json
import os
import traceback

import yaml

from benchmark import Benchmark
from checker import Checker
from loopy_llm import LLM, PromptConfig


class LoopyPipeline:
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
    ):
        self.benchmark = benchmark
        self.checker = checker
        self.model = model
        self.debug = debug
        self.log_path = log_path

        self.num_healing_retries = num_healing_retries
        self.heal_errors = heal_errors
        self.heal_errors_input = heal_errors_input

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
        self.llm = LLM(prompt_configs, healing_prompt_configs, self.model, self.debug)

        if "llm_input_dir" not in config:
            config["llm_input_dir"] = "llm_input"
        if "checker_input_dir" not in config:
            config["checker_input_dir"] = "checker_input"
        if self.benchmark is None:
            self.benchmark = Benchmark(
                config["llm_input_dir"], config["checker_input_dir"]
            )
        else:
            self.benchmark.llm_input_path = config["llm_input_dir"]
            self.benchmark.checker_input_path = config["checker_input_dir"]
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
        log_file = open(self.log_path, "w", encoding="utf-8")
        recheck_logs = None

        for i, instance in enumerate(
            self.benchmark.instances[start_index : start_index + max_benchmarks]
        ):
            if recheck_logfile is not None and os.path.exists(recheck_logfile):
                with open(recheck_logfile, "r", encoding="utf-8") as f:
                    recheck_logs = json.load(f)

            print(
                "Running benchmark: {i}/{n}".format(
                    i=i, n=len(self.benchmark.instances)
                )
            )
            instance_log_json = {"file": instance.llm_input_path}
            try:
                if recheck_logs is None:
                    llm_outputs, conversations = self.llm.run(
                        {"code": instance.llm_input}
                    )
                else:
                    llm_outputs, conversations = (
                        recheck_logs["logs"][i]["final_code_outputs"],
                        recheck_logs["logs"][i]["primary_conversation"],
                    )

                checker_input = self.benchmark.combine_llm_outputs(
                    instance.checker_input,
                    [
                        llm_output
                        for llm_output in llm_outputs
                        if not llm_output.startswith("ERROR")
                    ],
                )
                success, checker_message = self.checker.check(checker_input)

                instance_log_json["llm_conversation"] = conversations
                instance_log_json["final_code_outputs"] = llm_outputs
                instance_log_json[
                    "checker_input_without_invariants"
                ] = instance.checker_input
                instance_log_json["checker_input_with_invariants"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    pruned_code = self.checker.prune_annotations_and_check(
                        checker_input
                    )
                    success, checker_message = self.checker.check(pruned_code)

                    instance_log_json["code_after_prune"] = pruned_code
                    instance_log_json["checker_output_after_prune"] = success
                    instance_log_json["checker_message_after_prune"] = checker_message

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
        log_file = open(self.log_path, "w", encoding="utf-8")
        for i, instance in enumerate(
            error_logs[start_index : start_index + max_benchmarks]
        ):
            if instance["checker_output_after_prune"] or instance["checker_output"]:
                print(
                    "Skipping successful benchmark: {i}/{n}".format(
                        i=i, n=len(error_logs)
                    )
                )
                continue

            print("Healing benchmark: {i}/{n}".format(i=i, n=len(error_logs)))
            instance_log_json = { "file": instance["file"] }
            try:
                success = False
                num_retries = 0
                instance_log_json["healing_conversations"] = []

                failed_checker_input = instance["checker_input_with_invariants"]
                checker_error_message = instance["checker_message"]
                while not success and num_retries < self.num_healing_retries:
                    healing_json = {}
                    llm_outputs, conversations = self.llm.heal(
                        input={
                            "code": failed_checker_input,
                            "error": checker_error_message,
                            "incorrect_invariants": self.checker.get_incorrect_invariants(
                                failed_checker_input, checker_error_message
                            ),
                        }
                    )

                    checker_input = self.benchmark.combine_llm_outputs(
                        instance["checker_input_without_invariants"], llm_outputs
                    )
                    success, checker_message = self.checker.check(checker_input)

                    healing_json["conversation"] = conversations
                    healing_json["final_code_outputs"] = llm_outputs
                    healing_json["checker_input_without_invariants"] = instance["checker_input_without_invariants"]
                    healing_json["checker_input_with_old_invariants"] = instance["checker_input_with_invariants"]
                    healing_json["input_error_message"] = instance["checker_message"]
                    healing_json["checker_input_with_new_invariants"] = checker_input
                    healing_json["checker_output"] = success
                    healing_json["checker_message"] = checker_message

                    if not success:
                        pruned_code = self.checker.prune_annotations_and_check(
                            checker_input
                        )
                        success, prune_checker_message = self.checker.check(pruned_code)
                        healing_json["code_after_prune"] = pruned_code
                        healing_json["checker_output_after_prune"] = success
                        healing_json["checker_message_after_prune"] = prune_checker_message

                        failed_checker_input = checker_input
                        checker_error_message = checker_message

                    instance_log_json["healing_conversations"].append(healing_json)
                    num_retries += 1

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
            json.dumps({"heal_input" : self.heal_errors_input, "logs": log_json, "stats": stats}, indent=4, ensure_ascii=False)
        )
        log_file.close()

        return

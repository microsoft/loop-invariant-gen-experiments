import datetime
import json
import os
import re
import subprocess
import traceback
from copy import deepcopy

import yaml
from jinja2 import Environment, FileSystemLoader
from llm_client import LLMClient
from llm_utils import Settings
from utils import ConvTree, Node


class BenchmarkInstance:
    def __init__(self, llm_input=None, checker_input=None):
        self.llm_input = llm_input
        self.checker_input = checker_input

    def __repr__(self) -> str:
        return f"BenchmarkInstance(data={self.llm_input}, checker_input={self.checker_input})"

    def __str__(self) -> str:
        return self.__repr__()


class Benchmark:
    def __init__(self, llm_input_dir="", checker_input_dir=""):
        self.llm_input_path = llm_input_dir
        self.checker_input_path = checker_input_dir
        self.instances: list[BenchmarkInstance] = []

    def load_instances(self):
        if self.llm_input_path == "" or not os.path.exists(self.llm_input_path):
            raise Exception("LLM input directory path not found")
        llm_input_files = os.listdir(
            os.path.join(os.path.dirname(__file__), self.llm_input_path)
        )
        llm_input_files = sorted(llm_input_files, key=lambda x: int(x.split(".")[0]))

        # TODO: Move this to a separate function. Ideally take in a transform function
        # that can be applied to the LLM input. For now, just read the dir as is.
        if self.checker_input_path == "" or not os.path.exists(self.checker_input_path):
            raise Exception("Checker input directory path not found")
        checker_input_files = os.listdir(
            os.path.join(os.path.dirname(__file__), self.checker_input_path)
        )
        checker_input_files = sorted(
            sorted(checker_input_files), key=lambda x: int(x.split(".")[0])
        )

        if len(llm_input_files) != len(checker_input_files):
            raise Exception(
                "Number of LLM input files and checker input files do not match"
            )
        for x, y in zip(llm_input_files, checker_input_files):
            llm_input = None
            checker_input = None
            with open(os.path.join(self.llm_input_path, x)) as f:
                llm_input = f.read()
            with open(os.path.join(self.checker_input_path, y)) as f:
                checker_input = f.read()
            self.instances.append(
                BenchmarkInstance(
                    llm_input=llm_input,
                    checker_input=checker_input,
                )
            )

    def combine_llm_outputs(self, checker_input, llm_outputs):
        if not any("insert invariant" in line for line in checker_input.splitlines()):
            print(f"Ignoring since no insert invariant keyword")
            return ""

        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                if "invariant" in line and "insert invariants" not in line:
                    invariants.append(line.strip())

        lines = checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "insert invariant" in line:
                loc = index
                break
        if loc is not None:
            lines = lines[: loc + 1] + invariants + lines[loc + 1 :]
        else:
            raise Exception("No 'insert invariant' found")
        output = "\n".join(lines)

        return output


class Checker:
    def __init__(self, name="boogie"):
        self.name = name

    def check(self, code):
        with open("/tmp/temp_eval.bpl", "w") as f:
            f.write(code)

        cmd = f"boogie /tmp/temp_eval.bpl /timeLimit:10"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        output = output.decode()

        if "1 verified" in output:
            return True, output
        else:
            return False, output

    def is_invariant(self, line):
        return "invariant" in line

    def get_line_no_from_error_msg(self, error_string):
        pattern = r"\((\d+),\d+\): Error"
        matches = re.findall(pattern, error_string)
        line_numbers = [int(match) - 1 for match in matches]

        pattern = r"\((\d+),\d+\): error"
        matches = re.findall(pattern, error_string)
        line_numbers2 = [int(match) - 1 for match in matches]
        line_numbers = line_numbers + line_numbers2

        return line_numbers

    def get_incorrect_invariants(self, code, error):
        line_numbers = self.get_line_no_from_error_msg(error)
        lines = code.splitlines()
        incorrect_invariants = []
        for line_number in line_numbers:
            if self.is_invariant(lines[int(line_number)]):
                incorrect_invariants.append(lines[int(line_number)].strip())
        return "\n".join(incorrect_invariants)

    def prune_annotations_and_check(self, input_code):
        while True:
            status, error_string = self.check(input_code)
            invariant_line_mapping = {}
            lines = input_code.splitlines()
            for no, line in enumerate(lines):
                if self.is_invariant(line):
                    invariant_line_mapping[no] = line
            if len(invariant_line_mapping) == 0:
                raise Exception("No invariants found")

            (invariant_line_start, invariant_line_end) = (
                list(invariant_line_mapping.keys())[0],
                list(invariant_line_mapping.keys())[-1],
            )

            line_numbers = self.get_line_no_from_error_msg(error_string)
            incorrect_invariant_line_numbers = [
                no for no in line_numbers if no in invariant_line_mapping.keys()
            ]
            correct_invariant_line_numbers = [
                i
                for i in list(invariant_line_mapping.keys())
                if i not in incorrect_invariant_line_numbers
            ]

            if len(incorrect_invariant_line_numbers) == 0:
                break
            if len(correct_invariant_line_numbers) == 0:
                print("No correct invariants found")
                break
            new_lines = (
                lines[:invariant_line_start]
                + [lines[i] for i in correct_invariant_line_numbers]
                + lines[invariant_line_end + 1 :]
            )
            new_code = "\n".join(new_lines)
            input_code = new_code
            status, _ = self.check(input_code)
            if status:
                break

        return input_code


class PromptConfig:
    def __init__(
        self,
        prompt_file=None,
        temperature=0.7,
        num_completions=1,
        set_output=None,
        dir=None,
    ):
        self.prompt_file = prompt_file
        self.temperature = temperature
        self.num_completions = num_completions
        self.set_output = set_output
        self.dir = os.path.join(os.path.dirname(__file__), dir)

    def __repr__(self) -> str:
        return "<PromptConfig prompt_file: {}, temperature: {}, num_completions: {}, set_output: {}>".format(
            self.prompt_file, self.temperature, self.num_completions, self.set_output
        )

    def render(self, input):
        template = Environment(loader=FileSystemLoader(self.dir)).get_template(
            self.prompt_file
        )
        prompt = template.render(input)
        return prompt

    def render_fixed_output(self, input):
        template = Environment(loader=FileSystemLoader(self.dir)).get_template(
            self.set_output
        )
        prompt = template.render(input)
        return prompt

    def from_file(self, input):
        if type(input) == str:
            self.prompt_file = input
        elif type(input) == dict:
            self.prompt_file = list(input.items())[0][0]
            for k, v in list(input.items())[0][1].items():
                setattr(self, k, v)
        else:
            raise Exception("Invalid input type")
        return self


class LLM:
    def __init__(
        self,
        prompt_configs=None,
        healing_prompt_configs=None,
        model="gpt-3.5-turbo",
        debug=False,
    ):
        self.prompt_configs = prompt_configs
        self.healing_prompt_configs = healing_prompt_configs
        self.model = model
        self.debug = debug

    def __repr__(self) -> str:
        return "<LLM prompt_configs: {}, healing_prompt_configs: {}, model: {}>".format(
            self.prompt_configs, self.healing_prompt_configs, self.model
        )

    def extract_code(self, output):
        lines = output.split("\n")
        line_nos = []
        for i, line in enumerate(lines):
            if "```" in line:
                line_nos.append(i)
        if len(line_nos) != 2:
            raise Exception("Output does not contain 1 code block")
        return "\n".join(lines[line_nos[0] + 1 : line_nos[1]])

    def run__(self, input, configs):
        responses = None
        conversation = ConvTree(
            Node(
                {
                    "role": "system",
                    "content": "You are a helpful AI software assistant that reasons about how code behaves.",
                }
            )
        )

        for prompt_config in configs:
            if prompt_config.set_output:
                latest = conversation.get_latest()
                user_node = Node(
                    {"role": "user", "content": prompt_config.render(input)}
                )
                assistant_node = Node(
                    {
                        "role": "assistant",
                        "content": prompt_config.render_fixed_output(input),
                    }
                )
                for node in latest:
                    user_node_ = deepcopy(user_node)
                    assistant_node_ = deepcopy(assistant_node)
                    user_node_.add_child(assistant_node_)
                    node.add_child(user_node_)
            else:
                llm_client = LLMClient(
                    Settings(
                        model=self.model,
                        temperature=prompt_config.temperature,
                        num_completions=prompt_config.num_completions,
                        debug=self.debug,
                    )
                )
                latest = conversation.get_latest()

                for node in latest:
                    last_node = deepcopy(
                        Node({"role": "user", "content": prompt_config.render(input)})
                    )
                    node.add_child(last_node)

                    (_, responses) = llm_client.chat(last_node.path_to_root())

                    for response in responses:
                        response_node = Node({"role": "assistant", "content": response})
                        last_node.add_child(response_node)

        latest = conversation.get_latest()
        return_code = []
        return_logs = conversation.get_full_tree()
        for response in latest:
            return_code.append(self.extract_code(response.data["content"]))

        return return_code, return_logs

    def run(self, input):
        return self.run__(input, self.prompt_configs)

    def heal(self, input):
        return self.run__(input, self.healing_prompt_configs)


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

    def run(self, max_benchmarks=1, start_index=0):
        if self.llm is None:
            raise Exception(
                "LLM not initialized. Call load_config first, to load input and prompt files."
            )

        if self.heal_errors:
            return self.heal(max_benchmarks, start_index)

        log_json = []
        stats = {"success": [], "failure": [], "total": 0}
        log_file = open(self.log_path, "w", encoding="utf-8")
        for i, instance in enumerate(
            self.benchmark.instances[start_index : start_index + max_benchmarks]
        ):
            print(
                "Running benchmark: {i}/{n}".format(
                    i=i, n=len(self.benchmark.instances)
                )
            )
            instance_log_json = {}
            try:
                llm_outputs, conversations = self.llm.run({"code": instance.llm_input})
                checker_input = self.benchmark.combine_llm_outputs(
                    instance.checker_input, llm_outputs
                )
                success, checker_message = self.checker.check(checker_input)

                instance_log_json["primary_conversation"] = conversations
                instance_log_json["final_code_outputs"] = llm_outputs
                instance_log_json["raw_checker_code"] = instance.checker_input
                instance_log_json["checker_input"] = checker_input
                instance_log_json["checker_output"] = success
                instance_log_json["checker_message"] = checker_message

                if not success:
                    pruned_code = self.checker.prune_annotations_and_check(
                        checker_input
                    )
                    success, checker_message = self.checker.check(pruned_code)

                    instance_log_json["checker_output_after_prune"] = success
                    instance_log_json["checker_message_after_prune"] = checker_message
                    instance_log_json["code_after_prune"] = pruned_code

                if success:
                    stats["success"].append(i)
                else:
                    stats["failure"].append(i)
                stats["total"] += 1

                log_json.append(instance_log_json)
            except Exception as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                log_json.append(instance_log_json)
                stats["failure"].append(i)
                stats["total"] += 1
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
        with open("healing_" + self.heal_errors_input, "r", encoding="utf-8") as f:
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
            instance_log_json = {}
            try:
                success = False
                num_retries = 0
                instance_log_json["healing_conversations"] = []

                failed_checker_input = instance["checker_input"]
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
                        instance["raw_checker_code"], llm_outputs
                    )
                    success, checker_message = self.checker.check(checker_input)

                    healing_json["final_code_outputs"] = llm_outputs
                    healing_json["conversation"] = conversations
                    healing_json["checker_input"] = checker_input
                    healing_json["checker_output"] = success
                    healing_json["checker_message"] = checker_message

                    if not success:
                        pruned_code = self.checker.prune_annotations_and_check(
                            checker_input
                        )
                        success, checker_message = self.checker.check(pruned_code)
                        healing_json["code_after_prune"] = pruned_code
                        healing_json["checker_output_after_prune"] = success
                        healing_json["checker_message_after_prune"] = checker_message

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
            except Exception as e:
                print(traceback.format_exc())
                instance_log_json["error"] = str(e)
                log_json.append(instance_log_json)
                stats["failure"].append(i)
                stats["total"] += 1
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

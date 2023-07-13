import re
import subprocess
from copy import deepcopy

import yaml
from jinja2 import Environment, FileSystemLoader
from llm_client import LLMClient
from llm_utils import Settings
from utils import ConvTree, Node

"""We need the following to abstract the pipeline
1. Raw input benchmark
2. Prompt(s) to be used
3. Take raw input/transformed input and combine with LLM output
4. Take combined output and invoke the checker
5. "Prune" annotations/invariants and retry invoking the checker
6. Take the combined output + error and heal with the LLM
7. Redo steps 3-5 for a fixed number of iterations

Pipeline:
Raw input + prompt to the LLM 
    - multiple stages in the prompt
    - each stage could have different inputs
    - some stages could have multiple completions

Raw input transformed to checker input
LLM output + checker input to checker

Prune annotations/invariants and retry
LLM output + checker input + error to LLM
    - multiple stages in the prompt
    - each stage could have different inputs
    - some stages could have multiple completions
Repeat for 15 times
"""

PROMPT_TEMPLATES_DIR = "../pipeline/templates/"

class Benchmark:
    def __init__(self, data = None):
        self.data = data

    def add_llm_outputs(self, checker, llm_output):
        return self.data, llm_output


class Checker:
    def __init__(self, command = None):
        self.command = command

    def check(self, code, print_output=False, print_command=False):
        with open("/tmp/temp_eval.bpl", "w") as f:
            f.write(code)
            
        cmd = f'boogie /tmp/temp_eval.bpl /timeLimit:10'
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        output = output.decode()

        if print_command:
            print(cmd)

        if print_output:
            print(output)

        if "1 verified" in output:
            return True, output
        else:
            return False, output

    def prune_annotations_and_check(self, input):
        return False

class PromptConfig:
    def __init__(self, prompt_file = None, temperature = 0.7, num_completions = 1, set_output = None):
        self.prompt_file = prompt_file
        self.temperature = temperature
        self.num_completions = num_completions
        self.set_output = set_output

    def __repr__(self) -> str:
        return "<PromptConfig prompt_file: {}, temperature: {}, num_completions: {}, set_output: {}>".format(self.prompt_file, self.temperature, self.num_completions, self.set_output)

    def render(self, input):
        template = Environment(loader=FileSystemLoader(PROMPT_TEMPLATES_DIR)).get_template(self.prompt_file)
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
    def __init__(self, prompt_configs = None, healing_prompt_configs = None):
        self.prompt_configs = prompt_configs
        self.healing_prompt_configs = healing_prompt_configs

    def __repr__(self) -> str:
        return "<LLM prompt_configs: {}, healing_prompt_configs: {}>".format(self.prompt_configs, self.healing_prompt_configs)

    def run(self, input, configs):
        responses = None
        conversation = ConvTree(
            Node(
                {"role": "system", "content": "You are a helpful AI software assistant that reasons about how code behaves."}
            )
        )

        for prompt_config in configs:
            if prompt_config.set_output:
                latest = conversation.get_latest()
                user_node = Node({"role": "user", "content": prompt_config.render(input)})
                assistant_node = Node({"role": "assistant", "content": prompt_config.render(input)})
                for node in latest:
                    user_node_ = deepcopy(user_node)
                    assistant_node_ = deepcopy(assistant_node)
                    user_node_.add_child(assistant_node_)
                    node.add_child(user_node_)
            else:
                llm_client = LLMClient(
                    Settings(
                        model='gpt-4',
                        temperature=prompt_config.temperature,
                        num_completions=prompt_config.num_completions,
                    )
                )
                latest = conversation.get_latest()
                
                for node in latest:
                    last_node = deepcopy(Node({"role": "user", "content": prompt_config.render(input)}))
                    node.add_child(last_node)
                    
                    (_, responses) = llm_client.chat(str(last_node.path_to_root()))

                    for response in responses:
                        response_node = Node({"role": "assistant", "content": response})
                        last_node.add_child(response_node)

        return responses

    def run(self, input):
        return self.run(input, self.prompt_configs)
    
    def heal(self, input):
        return self.run(input, self.healing_prompt_configs)


class LoopyPipeline:
    def __init__(self, 
            benchmark : Benchmark = None, 
            checker : Checker = None, 
            llm : LLM = None, 
            num_retries = 5):
        self.benchmark = benchmark
        self.checker = checker
        self.llm = llm
        self.num_retries = num_retries

    def from_file(self, config_file):
        config = yaml.load(open(config_file, "r"), Loader=yaml.FullLoader)

        prompt_configs = []
        if "prompts" not in config:
            raise Exception("No prompts specified in config file")
        for prompt_config in config["prompts"]:
            prompt_configs.append(PromptConfig().from_file(prompt_config))

        healing_prompt_configs = []
        if "healing_prompts" not in config:
            raise Exception("No healing prompts specified in config file")
        for healing_prompt_config in config["healing_prompts"]:
            healing_prompt_configs.append(PromptConfig().from_file(healing_prompt_config))

        checker = Checker(config["checker_cmd"])
        benchmark = Benchmark(config["benchmark"])
        llm = LLM(prompt_configs, healing_prompt_configs)

        self.benchmark = benchmark
        self.checker = checker
        self.llm = llm
        self.num_retries = config["num_retries"]

        return self

    def run(self):
        raw_input = self.benchmark.data
        llm_outputs = self.llm.run(raw_input)
        checker_input = self.benchmark.add_llm_outputs(self.checker, llm_outputs)
        success = self.checker.check(checker_input)
        if not success:
            success = self.checker.prune_annotations_and_check(checker_input)

        num_retries = 0
        while not success and num_retries < self.num_retries:
            llm_outputs = self.llm.heal(checker_input)
            checker_input = self.benchmark.add_llm_outputs(self.checker, llm_outputs)
            success = self.checker.check(checker_input)
            if not success:
                success = self.checker.prune_annotations_and_check(checker_input)
            num_retries += 1

        # return success


p = LoopyPipeline().from_file("config.yaml")
print(p.llm)


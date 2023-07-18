import datetime
import json
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

class BenchmarkInstance:
    def __init__(self, data = None, checker_input = None):
        self.data = data
        self.checker_input = checker_input

    def combine_llm_outputs(self, checker, llm_outputs):
        if checker.command == 'boogie':
            return self.add_boogie_llm_outputs(llm_outputs)
        else:
            print(f"Unknown checker: {checker}")
            raise Exception("Unknown checker: {}".format(checker))
        
    def add_boogie_llm_outputs(self, llm_outputs):

        if not any("insert invariant" in line for line in self.checker_input.splitlines()):
            print(f"Ignoring since no insert invariant keyword")
            return ""

        invariants = []
        for llm_output in llm_outputs:
            lines = llm_output.splitlines()
            for line in lines:
                if "invariant" in line and "insert invariants" not in line:
                    invariants.append(line.strip())

        lines = self.checker_input.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "insert invariant" in line:
                loc = index
                break
        if loc is not None:
            lines = lines[:loc+1] + invariants + lines[loc+1:]
        else:
            raise Exception("No \'insert invariant\' found")
        output = '\n'.join(lines)

        return output


class Checker:
    def __init__(self, command = None):
        self.command = command

    def check(self, code):
        with open("/tmp/temp_eval.bpl", "w") as f:
            f.write(code)
            
        cmd = f'boogie /tmp/temp_eval.bpl /timeLimit:10'
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        output, err = p.communicate()
        output = output.decode()

        if "1 verified" in output:
            return True, output
        else:
            return False, output

    def get_line_no_from_error_msg(self, error_string):
        pattern = r"\((\d+),\d+\): Error"
        matches = re.findall(pattern, error_string)
        line_numbers = [int(match)-1 for match in matches]

        pattern = r"\((\d+),\d+\): error"
        matches = re.findall(pattern, error_string)
        line_numbers2 = [int(match)-1 for match in matches]
        line_numbers = line_numbers + line_numbers2

        return line_numbers

    def prune_annotations_and_check(self, input_code):
        while True:
            status, error_string = self.check(input_code)
            invariant_line_mapping = {}
            lines = input_code.splitlines()
            for no, line in enumerate(lines):
                if "invariant" in line:
                    invariant_line_mapping[no] = line

            (invariant_line_start, invariant_line_end) = list(invariant_line_mapping.keys())[0], list(invariant_line_mapping.keys())[-1]

            line_numbers = self.get_line_no_from_error_msg(error_string)
            incorrect_invariant_line_numbers = [no for no in line_numbers if no in invariant_line_mapping.keys()]
            correct_invariant_line_numbers = [i for i in list(invariant_line_mapping.keys()) if i not in incorrect_invariant_line_numbers]

            if len(incorrect_invariant_line_numbers) == 0:
                break

            new_lines = lines[:invariant_line_start] + [lines[i] for i in correct_invariant_line_numbers] + lines[invariant_line_end+1:]
            new_code = "\n".join(new_lines)
            input_code = new_code
            status, _ = self.check(input_code)
            if status:
                break

        return input_code


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
    
    def render_fixed_output(self, input):
        template = Environment(loader=FileSystemLoader(PROMPT_TEMPLATES_DIR)).get_template(self.set_output)
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

    def extract_code(self, output):
        lines = output.split('\n')
        line_nos = []
        for i, line in enumerate(lines):
            if "```" in line:
                line_nos.append(i)
        if len(line_nos) != 2:
            raise Exception("Output does not contain 1 code block")
        return '\n'.join(lines[line_nos[0]+1:line_nos[1]])

    def run__(self, input, configs):
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
                assistant_node = Node({"role": "assistant", "content": prompt_config.render_fixed_output(input)})
                for node in latest:
                    user_node_ = deepcopy(user_node)
                    assistant_node_ = deepcopy(assistant_node)
                    user_node_.add_child(assistant_node_)
                    node.add_child(user_node_)
            else:
                llm_client = LLMClient(
                    Settings(
                        model='gpt-3.5-turbo',
                        temperature=prompt_config.temperature,
                        num_completions=prompt_config.num_completions,
                    )
                )
                latest = conversation.get_latest()
                
                for node in latest:
                    last_node = deepcopy(Node({"role": "user", "content": prompt_config.render(input)}))
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
    def __init__(self, 
            benchmark : BenchmarkInstance = None, 
            checker : Checker = 'boogie', 
            llm : LLM = None, 
            num_retries = 5):
        self.benchmark = benchmark
        self.checker = checker
        self.llm = llm
        self.num_retries = num_retries
        self.log_path = datetime.datetime.now().strftime("loopy_%Y_%m_%d_%H_%M_%S.json")

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
        benchmark = BenchmarkInstance(config["benchmark"])
        llm = LLM(prompt_configs, healing_prompt_configs)

        self.benchmark = benchmark
        self.checker = checker
        self.llm = llm
        self.num_retries = config["num_retries"]

        return self

    def run(self):
        log_json = {}
        log_file = open(self.log_path, "w")
        raw_input = self.benchmark.data
        llm_outputs, conversations = self.llm.run(raw_input)
        log_json["conversations"] = conversations
        checker_input = self.benchmark.combine_llm_outputs(self.checker, llm_outputs)
        log_json["checker_input"] = checker_input
        success, checker_message = self.checker.check(checker_input)
        log_json["checker_output"] = success
        log_json["checker_message"] = checker_message
        if not success:
            pruned_code = self.checker.prune_annotations_and_check(checker_input)
            success, checker_message = self.checker.check(pruned_code)
            log_json["pruned_checker_output"] = success
            log_json["pruned_checker_message"] = checker_message
            log_json["pruned_code"] = pruned_code

        num_retries = 0
        while not success and num_retries < self.num_retries:
            llm_outputs = self.llm.heal(checker_input)
            checker_input = self.benchmark.add_llm_outputs(self.checker, llm_outputs)
            success = self.checker.check(checker_input)
            if not success:
                success = self.checker.prune_annotations_and_check(checker_input)
            num_retries += 1

        log_file.write(json.dumps(log_json))
        log_file.close()

        return success

p = LoopyPipeline().from_file("config.yaml")
b = BenchmarkInstance({"c_code" : """int main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  (x = 1);
  (y = 0);
  // loop body
  while ((y < 1000)) {
    {
    (x  = (x + y));
    (y  = (y + 1));
    }

  }
  // post-condition
assert( (x >= y) );
}"""},
"""
procedure main() {
var nondet: bool;
var x: int;
var y: int;
x := 1;
y := 0;
while(y < 100000)
// insert invariants 
{
x := x + y;
y := y + 1;
}
assert(x >= y);
}""")
c = Checker("boogie")
p.benchmark = b
p.checker = c
p.run()
# p.llm.run({"c_code" : """int main() """})


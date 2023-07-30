import os
from copy import deepcopy

from jinja2 import Environment, FileSystemLoader
from llm_client import LLMClient
from llm_utils import Settings
from utils import ConvTree, Node


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
        system_message=None,
        prompt_configs=None,
        healing_prompt_configs=None,
        nudge_prompt_configs=None,
        model="gpt-3.5-turbo",
        debug=False,
    ):
        self.system_message = system_message
        self.prompt_configs = prompt_configs
        self.healing_prompt_configs = healing_prompt_configs
        self.nudge_prompt_configs = nudge_prompt_configs
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
        if len(line_nos) < 2:
            return (
                ("ERROR: Output does not contain at least 1 code block") + "\n" + output
            )
        return "\n".join(lines[line_nos[0] + 1 : line_nos[1]])

    def run__(self, input, configs, input_tree=None, output_full_tree=False):
        responses = None
        if input_tree is not None:
            conversation = input_tree
        else:
            conversation = ConvTree(
                Node(
                    {
                        "role": "system",
                        "content": "You are a helpful AI software assistant that reasons about how code behaves." if self.system_message is None else self.system_message,
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
        return_logs = None
        if output_full_tree:
            return_logs = deepcopy(conversation)
        else:
            return_logs = conversation.get_full_tree()
        for response in latest:
            return_code.append(self.extract_code(response.data["content"]))

        return return_code, return_logs

    def run(self, input, input_tree=None, output_full_tree=False):
        return self.run__(input, self.prompt_configs, input_tree, output_full_tree)
    
    def nudge(self, input_tree=None, output_full_tree=False):
        return self.run__(configs=self.nudge_prompt_configs, input_tree=input_tree, output_full_tree=output_full_tree)

    def heal(self, input):
        return self.run__(input, self.healing_prompt_configs)

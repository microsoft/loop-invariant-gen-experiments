from datetime import datetime
import json
import os
import re
from copy import deepcopy
import warnings

from jinja2 import Environment, FileSystemLoader

from llm_api_client import LLMAPIClient
from local_llm import LLMLocalClient
from llm_utils import Settings
from utils import ConvTree, Node


class Prompt:
    def __init__(
        self,
        system_text_file: str = None,
        prompt_text_file: str = None,
        temperature: float = 0.7,
        num_completions: int = 1,
        batch_size: int = 5,
        set_output: str = None,
    ):
        self.system_text_file = system_text_file
        self.prompt_text_file = prompt_text_file
        self.temperature = temperature
        self.num_completions = num_completions
        self.batch_size = batch_size
        self.set_output = set_output

    def get_system_text(self):
        template = Environment(
            loader=FileSystemLoader(os.path.join(os.path.dirname(__file__), "../"))
        ).get_template(self.system_text_file)
        # System prompt should ideally not have any inputs
        return template.render()

    def get_user_text(self, input: dict = None):
        template = Environment(
            loader=FileSystemLoader(os.path.join(os.path.dirname(__file__), "../"))
        ).get_template(self.prompt_text_file)
        prompt = template.render(input)
        return prompt

    def get_assistant_text(self, input: dict = None):
        warnings.warn(
            "Usage of get_assistant_text is discouraged, refactor the LLM interaction and use get_user_text instead",
            UserWarning,
        )
        template = Environment(
            loader=FileSystemLoader(os.path.join(os.path.dirname(__file__), "../"))
        ).get_template(self.set_output)
        prompt = template.render(input)
        return prompt

    def from_file(self, input):
        if type(input) == dict:
            self.system_text_file = input["system_text"]
            self.prompt_text_file = input["prompt_text"]
            self.temperature = (
                0.7 if "temperature" not in input else input["temperature"]
            )
            self.num_completions = (
                1 if "num_completions" not in input else input["num_completions"]
            )
            self.batch_size = 5 if "batch_size" not in input else input["batch_size"]
            self.set_output = None if "set_output" not in input else input["set_output"]
        else:
            raise Exception("Invalid input type for prompt")
        return self


class LLM:
    def __init__(
        self,
        model="gpt-3.5-turbo",
        debug=False,
    ):
        self.model = model
        self.debug = debug

    def extract_code(self, output, filter=lambda x: True):
        """
        Extracts the first code block that returns true
        for the filter function. We adhere to markdown
        format since it has shown to be very robust in
        the case of LLMs.
        """
        lines = output.split("\n")
        line_nos = []

        for i, line in enumerate(lines):
            if "```" in line:
                line_nos.append(i)

        if len(line_nos) < 2:
            return (
                "ERROR: Output does not contain at least 1 complete code block"
            ), output

        annotation_block = ""
        line_nos = (
            line_nos if len(line_nos) % 2 == 0 else line_nos[:-1]
        )  # skip the last block if it is incomplete

        for i in range(0, len(line_nos), 2):
            snippet = "\n".join(lines[line_nos[i] + 1 : line_nos[i + 1]])
            if filter(snippet):
                annotation_block = snippet
                break

        return (
            annotation_block
            if len(annotation_block) > 0
            else "\n".join(
                lines[line_nos[0] + 1 : line_nos[1]]
            )  # return the first code block if no annotation block is found
        )

    def extract_label(self, output):
        # TODO: Clean this up
        label_start = output.find("<label>")
        label_end = output.find("</label>")
        if label_start == -1 or label_end == -1:
            return None

        return output[label_start + len("<label>") : label_end].strip().lower()

    def chat_completion(
        self,
        input: dict = None,
        prompt: Prompt = None,
        label_only: bool = False,
        extraction_filter=lambda x: True,
    ):
        responses = None
        if prompt is None:
            raise Exception("No prompt supplied to chat_completion")

        system_message = {
            "role": "system",
            "content": ""
            if prompt.system_text_file is None
            else prompt.get_system_text(),
        }
        user_message = {
            "role": "user",
            "content": prompt.get_user_text(input),
        }

        llm_client = LLMAPIClient(
            Settings(
                model=self.model,
                temperature=prompt.temperature,
                num_completions=prompt.num_completions,
                debug=self.debug,
            )
        )

        (_, responses) = llm_client.chat([system_message, user_message])

        response_logs = [system_message, user_message] + responses

        response_blocks = []
        for response in responses:
            if label_only:
                response_blocks.append(self.extract_label(response))
            else:
                response_blocks.append(self.extract_code(response, extraction_filter))

        return response_blocks, response_logs

    def generate_annotation(
        self,
        input: dict = None,
        prompt: Prompt = None,
        label_only: bool = False,
        extraction_filter=lambda x: True,
    ):
        return self.chat_completion(
            input=input,
            prompt=prompt,
            label_only=label_only,
            extraction_filter=extraction_filter,
        )

    def heal(
        self,
        input: dict = None,
        prompt: Prompt = None,
        label_only: bool = False,
        extraction_filter=lambda x: True,
    ):
        return self.chat_completion(
            input=input,
            prompt=prompt,
            label_only=label_only,
            extraction_filter=extraction_filter,
        )

    def generate_annotations_local(self, inputs: [dict] = [], prompt: Prompt = None):
        dataset_dump = []

        system_text = (
            "" if prompt.system_text_file is None else prompt.get_system_text()
        )

        for input in inputs:
            system_message = {"role": "system", "content": system_text}
            user_message = {
                "role": "user",
                "content": prompt.get_user_text(input),
            }
            dataset_dump.append(
                {"file": input[0], "input": [system_message, user_message]}
            )

        dataset_path = datetime.now().strftime(
            f"local_llm_dataset_%Y_%m_%d_%H_%M_%S.json"
        )
        with open(dataset_path, "w", encoding="utf-8") as f:
            json.dump(dataset_dump, f, indent=4, ensure_ascii=False)

        print("Dataset dumped to {}".format(dataset_path))

        llm_client = LLMLocalClient(
            Settings(
                temperature=prompt.temperature,
                num_completions=prompt.num_completions,
                max_batch_size=prompt.batch_size,
            )
        )
        output_file = llm_client.chat_batch(dataset_path)

        print("Reading output dumped to {}".format(output_file))
        output = None

        with open(output_file, "r", encoding="utf-8") as f:
            output = json.load(f)
        return output

import json
import subprocess
from llm import LLMClient


class LLMLocalClient(LLMClient):
    def __init__(self, settings):
        super().__init__(settings)

    def chat_batch(self, dataset_path: str):
        """This should be for the local LLM client."""

        cmd = f"OMP_NUM_THREADS=4 torchrun --nproc_per_node 4 llama_2.py --inputs {dataset_path}"
        p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
        # output, err = p.communicate()
        # output = output.decode("utf-8")

        print(p)


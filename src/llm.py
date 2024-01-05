from llm_utils import Settings


class LLMClient:
    def __init__(self, settings: Settings):
        self.settings = settings

    def chat(self, messages):
        """This should be for the LLM API client."""
        raise NotImplementedError


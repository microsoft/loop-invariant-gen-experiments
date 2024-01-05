from llm_utils import Settings


class LLMClient:
    def __init__(self, settings: Settings):
        self.settings = settings

    def chat(self, messages):
        """This should be for the LLM API client."""
        raise NotImplementedError

    def chat_batch(self, messages_list):
        """This should be for the local LLM client."""
        raise NotImplementedError

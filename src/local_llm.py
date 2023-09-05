from llm import LLMClient


class LLMLocalClient(LLMClient):
    def __init__(self, settings):
        super().__init__(settings)

    def chat_batch(self, messages_list):
        """This should be for the local LLM client."""
        
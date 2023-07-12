import json
import os
import re
import time
from typing import Any, List, Optional

import openai
import requests
import tiktoken
from llm_utils import Logger, Settings


class LLMClient:
  """The LLM client."""

  def __init__(self, settings: Settings):
    """Configure this LLM client."""
    self.settings = settings
    self._model = settings.model
    self._max_tokens: int = settings.max_tokens
    self._temperature: float = settings.temperature
    self._num_completions: int = settings.num_completions
    # Values for implementing cool-down and retry logic.
    self._interval = 60 / settings.prompts_per_minute
    self._last_call_time = None
    self._max_retries: int = 5
    # Statistics.
    self.prompt_count: int = 0

  def prompt(self, prompt: str, system_message: str) -> tuple[bool, List[str]]:
    """Send the completion prompt and get the response from the model."""
    self.prompt_count += 1
    return self._send_chat_completion([{ "role": "system", "content": system_message },
                                       { "role": "user", "content": prompt }])

  def chat(self, messages: list[dict[str, str]]) -> tuple[bool, List[str]]:
    """Send the prompt and get the response from the model."""
    self.prompt_count += 1
    return self._send_chat_completion(messages)

  def _send_chat_completion(self, messages: list[dict[str, str]]) -> tuple[bool, List[str]]:
    """Send the chat completion prompt and get the response from the model."""
    # Check if the prompt passes the token limit, and if yes, try to upgrade the model.
    prompt = self._messages_to_string(messages)
    model = self._check_and_upgrade_context_size(prompt, self._model)

    # Enforce a cool-down for rate-limiting.
    current_time = time.time()
    if self._last_call_time is not None and (current_time - self._last_call_time) < self._interval:
      time.sleep(self._interval)

    attempt: int = 0
    while attempt < self._max_retries:
      try:
        openai.api_key = self.settings.get_api_key()
        openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
        openai.api_type = "azure"
        openai.api_version = "2023-03-15-preview"
        
        # Make the request to the remote LLM API with retries.
        Logger.log_model_request(model, [message["content"] for message in messages])
        self._last_call_time = current_time
        response: Any = openai.ChatCompletion.create(
        	engine=self._get_deployment_name(model),
          messages = messages,
          max_tokens = self._max_tokens,
          temperature = self._temperature,
          n = self._num_completions,
          top_p = 1,
          frequency_penalty = 0,
          presence_penalty = 0,
          stop = None)
        completions = []
        for completion in response["choices"]:
          completions.append(completion["message"]["content"])
        return True, completions
      except Exception as e:
        attempt += 1
        Logger.log_error(f'Failed to send LLM prompt (attempt #{attempt}): {repr(e)}')
        seconds = re.search(r"retry after (\d+) seconds", str(e))
        if seconds:
            time.sleep(int(seconds.group(1)))
        else:
            time.sleep(2 * attempt)
        continue
    return False, ['Failed to prompt the LLM.']

  def _check_and_upgrade_context_size(self, prompt: str, model: str) -> str:
    """Checks if the context size passes the token limit and upgrades the model if possible."""
    try:
      self._enforce_token_limit(prompt, model)
    except Exception as e:
      is_upgradeable, new_model = self._upgrade_model_context_size(model)
      if is_upgradeable:
        Logger.log_info(f"Increasing context size by upgrading '{model}' to '{new_model}' for the next prompt.")
        model = new_model
        self._enforce_token_limit(prompt, model)
      else:
        raise e
    return model

  def _enforce_token_limit(self, prompt: str, model: str):
    """Enforces the token limit on the prompt for the specified model."""
    tokens_count: int = self._count_token_size(prompt, model)
    threshold = 0
    if model == 'text-davinci-003':
      threshold = 2500
    elif model == 'gpt-3.5-turbo':
      threshold = 2500
    elif model == 'gpt-4':
      threshold = 6000
    elif model == 'gpt-4-32k':
      threshold = 30000
    if tokens_count > threshold:
      raise Exception(f"Tokens size '{tokens_count}' exceeded the '{threshold}' limit.")

  def _count_token_size(self, prompt: str, model: str) -> int:
    """Return the number of tokens in the prompt."""
    encoding = tiktoken.encoding_for_model(model)
    num_tokens = len(encoding.encode(prompt))
    return num_tokens

  def _upgrade_model_context_size(self, model: str) -> tuple[bool, str]:
    """Tries to upgrade the mode to a larger available context size."""
    if model == 'gpt-4':
      return True, 'gpt-4-32k'
    return False, model

  def _messages_to_string(self, messages: list[dict[str, str]]) -> str:
    """Concatenates the list of messages to a string."""
    prompt = ''
    for message in messages:
      prompt += message['content']
    return prompt
    
  def _get_deployment_name(self, model: str) -> str:
    if model == 'gpt-3.5-turbo':
      return 'gpt-35-tunro'
    elif model in ['text-davinci-003', 'gpt-4', 'gpt-4-32k']:
      return model
    else:
      raise Exception(f"Model '{model}' is not an OpenAI model.")


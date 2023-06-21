#Note: The openai-python library support for Azure OpenAI is in preview.
import os
import openai
openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

response = openai.ChatCompletion.create(
  engine="gpt-4",
  messages = [{"role":"system","content":"You are an AI assistant that helps people find information."},{"role":"user","content":"Which model are you?"},{"role":"assistant","content":"I am an AI language model created by OpenAI called GPT-3. I can help with answering questions, providing information, and assisting with various tasks."},{"role":"user","content":"Are you GPT-4 or GPT-3?"},{"role":"assistant","content":"We're experiencing heavy traffic right now. Please try again at a later time."}],
  temperature=0.7,
  max_tokens=800,
  top_p=0.95,
  frequency_penalty=0,
  presence_penalty=0,
  stop=None)

print(response)
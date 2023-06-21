def prompt1(code):
    return f"""Consider the following C code

```c    
{code}
```    

Keep in mind:    
1. Uninitialized variables can have garbage values    

Let's think step by step about the following:    
1. What pre-conditions are given?
2. What the loop body does?    
3. What post-conditions are required?
4. What is the transfer function of the loop body?
"""

def prompt2():
    return """Think step by step about the following:
1. What is a loop invariant?
2. What conditions does a loop invariant need to satisfy to be correct in the given code snippet?
3. What loop invariants are necessary to prove the given code snippet? Work backward from the given postconditions.
"""

def prompt3():
    return """Given the above, generate Boogie code for the given code snippet with the loop invariants included.

Keep in mind:
1. Do not modify the semantics of the provide C code snippet. Translate C code as is to Boogie code and only insert invariants

```boogie
"""

def prompt4():
    return """Extract the invariants from the given Boogie code and output them in the following format:

Format:
invariant ...
invariant ...
...
"""

import os
import openai
from tenacity import retry, wait_exponential

openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

@retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(messages):
  completion = openai.ChatCompletion.create(
    engine="gpt-4",
    messages=messages,
    temperature=0.7,
    max_tokens=7000,
    top_p=0.95,
    frequency_penalty=0,
    presence_penalty=0,
    stop=None
  )
  return completion.choices[0].message.content

def conversation(code):
  prompts = [
    {"role": "system", "content": "You are an AI assistant that reasons about how code behaves"},
    {"role": "user", "content": prompt1(code)}
    ]
  response = call_llm(prompts)
  prompts.append({"role": "assistant", "content": response})
  prompts.append({"role": "user", "content": prompt2()})
  response = call_llm(prompts)
  prompts.append({"role": "assistant", "content": response})
  prompts.append({"role": "user", "content": prompt3()})
  response = call_llm(prompts)
  prompts.append({"role": "assistant", "content": response})
  prompts.append({"role": "user", "content": prompt4()})
  response = call_llm(prompts)
  return response
  
for i, file in enumerate(os.listdir("c_benchmark")):
    with open(f"c_benchmark/{file}") as f:
        if file != '26.c': continue
        code = f.read()
        out = conversation(code)
        # boogie_code = out.split('```')[1]
        with open(f"boogie_code/{file[:-2]}.bpl", "w") as f2:
            # f2.write(boogie_code)
            f2.write(out)
        print(i, file)

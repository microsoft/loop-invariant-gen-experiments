import os
from jinja2 import Environment, FileSystemLoader
import openai
from tenacity import retry, wait_exponential

model = "gpt-4"
print_prompts = False

openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

@retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(messages, num_completions=1, temperature=0.7):
  completion = openai.ChatCompletion.create(
    engine=model,
    messages=messages,
    temperature=temperature,
    max_tokens=4000,
    top_p=0.95,
    frequency_penalty=0,
    presence_penalty=0,
    stop=None,
    n=num_completions
  )
  if num_completions == 1:
    return completion.choices[0].message.content
  else:
    return [c.message.content for c in completion.choices]

def process_output(output):
  lines=output.splitlines()
  line_nos = []
  for i, line in enumerate(lines):
    if "```" in line:
        line_nos.append(i)
  if len(line_nos) != 2:
    raise Exception("Output does not contain 1 code block")
  return '\n'.join(lines[line_nos[0]+1:line_nos[1]])

def conversation(code, print_progress=False):
  environment = Environment(loader=FileSystemLoader("templates/"))
  prompts = [
    {"role": "system", "content": "You are a helpful AI software assistant that reasons about how code behaves."},
    {"role": "user", "content": environment.get_template("CoT1.txt").render(c_code=code)},
    ]
  
  response = call_llm(prompts)
  prompts.append({"role": "assistant", "content": response})
  if print_progress:
    print(prompts[-2]["content"])
    print(prompts[-1]["content"])
  
  prompts.append({"role": "user", "content": environment.get_template("CoT2.txt").render()})
  prompts.append({"role": "assistant", "content": environment.get_template("CoT2_answer.txt").render()})
  prompts.append({"role": "user", "content": environment.get_template("CoT3.txt").render()})
  # responses = [call_llm(prompts, 1)]
  responses = call_llm(prompts, num_completions=3)
  
  output_responses = []
  for res in responses:
    prompts.append({"role": "assistant", "content": res})
    if print_progress:
      print(prompts[-4]["content"])
      print(prompts[-3]["content"])
      print(prompts[-2]["content"])
      print(prompts[-1]["content"])
    
    prompts.append({"role": "user", "content": environment.get_template("CoT4.txt").render()})
    response = call_llm(prompts, temperature=0.1)
    prompts.append({"role": "assistant", "content": response})
    if print_progress:
      print(prompts[-2]["content"])
      print(prompts[-1]["content"])
    
    response = process_output(response)
    output_responses.append(response)
  
  return output_responses

# for i, file in enumerate(os.listdir("c_benchmark")):
#     if i <= 18: continue
#     with open(f"c_benchmark/{file}") as f:
#         # if file != '23.c': continue
#         code = f.read()
#         out = conversation(code, print_prompts)
#         # boogie_code = out.split('```')[1]
#         for j, o in enumerate(out):
#           with open(f"boogie_code/{file[:-2]}_{j}.bpl", "w") as f2:
#               # f2.write(boogie_code)
#               f2.write(o)
#         print(i, file)

i = 0
for src_root, dirs, files in os.walk('c_benchmarks'):
  if 'code2inv' in src_root: continue
  # if '/cav' not in src_root: continue
  for file in files:
    if file.endswith('.c'):
      file_path = os.path.join(src_root, file)
      print("Processing", file_path)
      out = conversation(open(file_path).read(), print_prompts)
      dst_root = src_root.replace('c_benchmarks', 'boogie', 1)
      os.makedirs(dst_root, exist_ok=True)
      for j, o in enumerate(out):
        # write output to file
        with open(f'{dst_root}/{file[:-2]}_{j}.bpl', 'w') as f:
          f.write(o)
      i += 1
      print(i, file)

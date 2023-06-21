import os
from jinja2 import Environment, FileSystemLoader
import openai
from tenacity import retry, wait_exponential
import subprocess
import re

NUM_RETRIES = 3

model = "gpt-3.5-turbo"

# openai.api_type = "azure"
# openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
# openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

# @retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(messages, num_completions=1, temperature=0.7):
	# completion = openai.ChatCompletion.create(
	#   engine=model,
	#   messages=messages,
	#   temperature=0.7,
	#   max_tokens=4000,
	#   top_p=0.95,
	#   frequency_penalty=0,
	#   presence_penalty=0,
	#   stop=None
	# )
	completion = openai.ChatCompletion.create(
		model=model,
		messages=messages,
		temperature=temperature,
		max_tokens=1000,
		top_p=0.95,
		frequency_penalty=0,
		presence_penalty=0,
		stop=None,
		n = num_completions
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

def conversation(boogie_code, boogie_error, incorrect_invariants, print_progress=False):
	environment = Environment(loader=FileSystemLoader("templates/"))
	prompts = [
		{"role": "system", "content": "You are a helpful AI software assistant that reasons about how code behaves."},
		{"role": "user", "content": environment.get_template("repair1.txt").render(boogie_code=boogie_code, boogie_error=boogie_error, incorrect_invariants='\n'.join(incorrect_invariants))},
		]
	
	response = call_llm(prompts)
	prompts.append({"role": "assistant", "content": response})
	if print_progress:
		print(prompts[-2]["content"])
		print(prompts[-1]["content"])
	
	prompts.append({"role": "user", "content": environment.get_template("repair2.txt").render()})
	responses = [call_llm(prompts, 1)]
#   responses = call_llm(prompts, num_completions=3)
	
	output_responses = []
	for res in responses:
		prompts.append({"role": "assistant", "content": res})
		if print_progress:
			print(prompts[-2]["content"])
			print(prompts[-1]["content"])
		
		prompts.append({"role": "user", "content": environment.get_template("repair3.txt").render()})
		response = call_llm(prompts, temperature=0.1)
		prompts.append({"role": "assistant", "content": response})
		if print_progress:
			print(prompts[-2]["content"])
			print(prompts[-1]["content"])
		
		response = process_output(response)
		output_responses.append(response)
	
	return output_responses

def evaluate_boogie_file(file_name):
	cmd = f'boogie {file_name}'
	p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
	output, err = p.communicate()
	output = output.decode()
	return output

def evaluate_boogie_code(code):
		with open("/tmp/temp_eval.bpl", "w") as f:
				f.write(code)
		return evaluate_boogie_file("/tmp/temp_eval.bpl")

def get_line_no_from_error_msg(error_string):
		# Define a regular expression to match the line numbers in the error message
		pattern = r"\((\d+),\d+\): Error"

		# Find all matches of the regular expression in the error message
		matches = re.findall(pattern, error_string)

		# Convert the matches to 0 indexed integers
		line_numbers = [int(match)-1 for match in matches]

		return line_numbers

def get_incorrect_invariant(code, error):
		line_numbers = get_line_no_from_error_msg(error)
		lines = code.splitlines()
		incorrect_invariants = []
		for line_number in line_numbers:
				if "invariant" in lines[line_number]:
						incorrect_invariants.append(lines[line_number].strip())
		return incorrect_invariants

def remove_incorrect_invariants(code, error):
		buggy_line_numbers = get_line_no_from_error_msg(error)
		lines = code.splitlines()
		output_lines = []
		for index, line in enumerate(lines):
				if index in buggy_line_numbers and "invariant" in line:
					continue
				else:
					output_lines.append(line)
		return '\n'.join(output_lines)

def strip_invariants_from_code(code):
		lines = code.splitlines()
		output_lines = []
		for index, line in enumerate(lines):
				if "invariant" in line:
					continue
				else:
					output_lines.append(line)
		return '\n'.join(output_lines)

def get_invariants_from_code(code):
		lines = code.splitlines()
		output_lines = []
		for index, line in enumerate(lines):
			if "invariant" in line:
				output_lines.append(line.strip())
		return output_lines

def splice_invariants(code, invariants):
		lines = code.splitlines()
		while_loop_line_no = None
		for index, line in enumerate(lines):
				if "while" in line:
						while_loop_line_no = index
						break
		if while_loop_line_no is None:
				raise Exception("Could not find while loop")
		output_lines = lines[:while_loop_line_no+1] + invariants + lines[while_loop_line_no+1:]
		return '\n'.join(output_lines)

def evaluate_boogie_code_after_partition(code):
		output = evaluate_boogie_code(code)
		if "1 verified" in output:
				return output
		else:
			partitioned_code = remove_incorrect_invariants(code, output)
			return partitioned_code, evaluate_boogie_code(partitioned_code)

for i, file in enumerate(os.listdir("boogie_code_removed_inv_failure")):
		with open(f"boogie_code_removed_inv_failure/{file}") as f:
				if file != '3.bpl': continue
				code = f.read()
				error = evaluate_boogie_file(f"boogie_code_removed_inv_failure/{file}")
				incorrect_invariants = get_incorrect_invariant(code, error)
				n = 0
				while n <= NUM_RETRIES:
						out = conversation(code, error, incorrect_invariants, print_progress=True)
						repaired_code = out[0]
						parsed_code = strip_invariants_from_code(code)
						invariants = get_invariants_from_code(repaired_code)
						new_code = splice_invariants(parsed_code, invariants)
						partitioned_code, error = evaluate_boogie_code_after_partition(new_code)
						if "1 verified" in error:
							with open(f"boogie_repaired/{file}", "w") as f:
									f.write(partitioned_code)
							break
						elif n == NUM_RETRIES:
							with open(f"boogie_repaired/{file}", "w") as f:
									f.write(new_code)
						else:
							code = new_code
							error = error
							incorrect_invariants = get_incorrect_invariant(code, error)
						n += 1
				print(i, file)
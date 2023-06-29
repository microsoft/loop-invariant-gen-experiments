import os
from jinja2 import Environment, FileSystemLoader
import openai
from tenacity import retry, wait_exponential
import subprocess
import re
import random

NUM_RETRIES = 10
SRC_DIR = "boogie_code_pruned_failure"
SUCCESS_DIR = "boogie_repaired_success"
FAILURE_DIR = "boogie_repaired_failure"

model = "gpt-4-32k"

openai.api_type = "azure"
openai.api_base = "https://gcrgpt4aoai6c.openai.azure.com/"
openai.api_version = "2023-03-15-preview"
openai.api_key = os.getenv("OPENAI_API_KEY")

@retry(wait=wait_exponential(multiplier=1, min=20, max=60))
def call_llm(messages, num_completions=1, temperature=0.7):
	completion = openai.ChatCompletion.create(
	  engine=model,
	  messages=messages,
	  temperature=0.7,
	  max_tokens=4000,
	  top_p=0.95,
	  frequency_penalty=0,
	  presence_penalty=0,
	  stop=None
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

		
		while True:
			try:
				response = process_output(response)
				break
			except Exception as e:
				print(f"Log - Error in processing LLM output: {e}")
				print("\nRetrying")
				prompts = prompts[:-1]
				response = call_llm(prompts, temperature=0.3*random.random())
				prompts.append({"role": "assistant", "content": response})
				if print_progress:
					print(prompts[-2]["content"])
					print(prompts[-1]["content"])

		output_responses.append(response)
	
	return output_responses

def evaluate_boogie_file(file_name):
	cmd = f'boogie /timeLimit:10 {file_name}'
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

		pattern = r"\((\d+),\d+\): error"

		matches = re.findall(pattern, error_string)

		line_numbers2 = [int(match)-1 for match in matches]

		# combine line_numbers and line_numbers2
		line_numbers = line_numbers + line_numbers2

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
				return code, output
		else:
			partitioned_code = remove_incorrect_invariants(code, output)
			return partitioned_code, evaluate_boogie_code(partitioned_code)

i = 0
for root, dirs, files in os.walk(SRC_DIR):
	for file in files:
		# if file != '110.bpl': continue
		print(f"Healing File - {file}")
		file_path = os.path.join(root, file)
		code = open(file_path).read()
		error = evaluate_boogie_file(file_path)
		incorrect_invariants = get_incorrect_invariant(code, error)
		n = 0
		while n <= NUM_RETRIES:
			print(f"Retry # {n}")
			out = conversation(code, error, incorrect_invariants, print_progress=True)
			# out = conversation(code, error, incorrect_invariants)
			repaired_code = out[0]
			parsed_code = strip_invariants_from_code(code)
			invariants = get_invariants_from_code(repaired_code)
			new_code = splice_invariants(parsed_code, invariants)
			partitioned_code, error = evaluate_boogie_code_after_partition(new_code)
			if "1 verified" in error:
				output_root = root.replace(SRC_DIR, SUCCESS_DIR, 1)
				os.makedirs(output_root, exist_ok=True)
				with open(os.path.join(output_root, file), "w") as f:
						f.write(partitioned_code)
				print(f"{file} - Success")
				break
			elif n == NUM_RETRIES:
				output_root = root.replace(SRC_DIR, FAILURE_DIR, 1)
				os.makedirs(output_root, exist_ok=True)
				with open(os.path.join(output_root, file), "w") as f:
						f.write(new_code)
				print(f"{file} - Failure")
			else:
				# code = random.choice([new_code, partitioned_code])
				code = new_code
				error = error
				incorrect_invariants = get_incorrect_invariant(code, error)
			n += 1
		i += 1
		print(i, file)

import os
import re
import subprocess

# Define regular expressions
while_loop_pattern = re.compile(r'while\s*\(.*\)\s*\{')
function_pattern = re.compile(r'\w+\s+\w+\s*\(.*\)\s*\{')
array_pattern = re.compile(r'\w+\s+\w+\s*\[.*\]\s*;')

def count_occurrences(file_path, pattern):
    with open(file_path, 'r') as file:
        data = file.read()
        return len(pattern.findall(data))

def search_c_files(directory):
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.endswith('.c'):
                file_path = os.path.join(root, file)
                while_count = count_occurrences(file_path, while_loop_pattern)
                func_count = count_occurrences(file_path, function_pattern)
                array_count = count_occurrences(file_path, array_pattern)

                if while_count > 1 or array_count > 0:
                    # print(f'File: {file_path}\nWhile Loops: {while_count}, Functions: {func_count}, Arrays: {array_count}\n')
                    os.remove(file_path)
                    print(f"Removed {file_path}")

# Starting directory
subprocess.run(['rm', '-rf', 'filtered_benchmarks/*'])
subprocess.run('cp -r translated_benchmarks/accelerating_invariant_generation filtered_benchmarks/'.split())
search_c_files("filtered_benchmarks/accelerating_invariant_generation")

import subprocess
import os
import sys

SCRIPT_PATH = 'lark_parser.py'
TRANSLATION_DIR = 'filtered_benchmarks/accelerating_invariant_generation/'
OUTPUT_DIR = 'checker_output/accelerating_invariant_generation/'

def run_codegen_script(script_path, input_path):
    """ Runs the codegen script and returns the output and status

    Args:
        script_path (str): Path to the python script
        input_path (str): Path to the input C code file

    Returns:
        dict: A dictionary containing 'output' (STDOUT), 'error' (STDERR), and 'returncode' (exit status)
    """

    # run the script and capture STDOUT and STDERR
    result = subprocess.run(['python', script_path, input_path], capture_output=True, text=True)

    # capture the output
    output = result.stdout
    # capture any errors
    error = result.stderr
    # capture the return code
    returncode = result.returncode

    return {'output': output, 'error': error, 'returncode': returncode}

def check_boogie_syntax(output):
    """ Checks the generated Boogie code for syntax errors

    Args:
        output (str): The generated Boogie code

    Returns:
        bool: True if the code is valid, False otherwise
    """
    # go through lines of output and remove lines containing "assert"
    # (these are the lines that contain the generated assertions)
    output = '\n'.join([line for line in output.split('\n') if 'assert' not in line])
    with open('/tmp/temp.bpl', 'w') as f:
        f.write(output)
    # run Boogie on the output
    result = subprocess.run(['boogie', '/tmp/temp.bpl'], capture_output=True, text=True)
    if '1 verified' in result.stdout:
        return True
    else:
        print(f"Boogie:\n{output}\n===\nError:\n{result.stdout}")
        return False


# Main Code
if sys.argv[1] == 'parser':
    if  os.path.exists('checker_output'):
        os.system('rm -rf checker_output')

    # If you've updated translated_benchmarks, remember to run filter.py to updated filtered_benchmarks
    for src_root, dirs, files in os.walk(TRANSLATION_DIR):
        for file in files:
            if file.endswith('.c'):
                file_path = os.path.join(src_root, file)
                result = run_codegen_script(SCRIPT_PATH, file_path)
                if result['returncode'] == 0:
                    # if dir doesn't exist, create it - dir name = "checker_output"
                    dst_root = src_root.replace(TRANSLATION_DIR, OUTPUT_DIR, 1)
                    os.makedirs(dst_root, exist_ok=True)
                    # write output to file
                    with open(f'{dst_root}/{file[:-2]}.bpl', 'w') as f:
                        f.write(result['output'])
                else:
                    print(f'Parser failed: {file_path}')
elif sys.argv[1] == 'boogie':
    for src_root, dirs, files in os.walk(os.path.join(OUTPUT_DIR, '')):
        for file in files:
            if file.endswith('.bpl'):
                file_path = os.path.join(src_root, file)
                result = check_boogie_syntax(open(file_path).read())
                if not result:
                    print(f'Failed: {file_path}')
                else:
                    print(f'Passed: {file_path}')
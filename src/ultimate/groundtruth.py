import json
import os
import subprocess
import sys

# add .. to path
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from frama_c import FramaCBenchmark
from llm_utils import ACTION, BOLD, END, FAIL, INFO, SUCCESS, WARNING


def remove_hash_define(code):
    fc_b = FramaCBenchmark()
    preproc_query = fc_b.language.query(
        """
        (preproc_def) @preprocessor
        """
    )
    ast = fc_b.parser.parse(bytes(code, "utf-8"))
    preprocessers = preproc_query.captures(ast.root_node)
    preprocessers = sorted(preprocessers, key=lambda x: x[0].start_byte, reverse=True)
    preprocess_map = {}
    for preprocessor in preprocessers:
        children_types = [child.type for child in preprocessor[0].children]
        if "identifier" == children_types[1] and "preproc_arg" == children_types[2]:
            preprocess_map[preprocessor[0].children[1].text.decode()] = (
                preprocessor[0].children[2].text.decode()
            )

    comment_query = fc_b.language.query(
        """
        (comment) @comment 
        """
    )
    comments = comment_query.captures(ast.root_node)
    comments = sorted(comments, key=lambda x: x[0].start_byte, reverse=True)
    comments = list(
        filter(
            lambda x: code[x[0].start_byte : x[0].end_byte].startswith("//@"), comments
        )
    )

    for i in range(len(comments)):
        ast = fc_b.parser.parse(bytes(code, "utf-8"))
        n_comments = comment_query.captures(ast.root_node)
        n_comments = sorted(n_comments, key=lambda x: x[0].start_byte, reverse=True)
        n_comments = list(
            filter(
                lambda x: code[x[0].start_byte : x[0].end_byte].startswith("//@"),
                n_comments,
            )
        )
        n_comments = list(
            filter(
                lambda x: any(
                    [y in code[x[0].start_byte : x[0].end_byte] for y in preprocess_map]
                ),
                n_comments,
            )
        )

        if len(n_comments) == 0:
            break

        n_comment_block = code[n_comments[0][0].start_byte : n_comments[0][0].end_byte]
        for key, value in preprocess_map.items():
            if key in n_comment_block:
                # remove //@ assert and replace hash defines
                n_comment_block = n_comment_block[:10] + n_comment_block[10:].replace(key, value)
        code = (
            code[: n_comments[0][0].start_byte]
            + n_comment_block
            + code[n_comments[0][0].end_byte :]
        )

    return code


def run_ultimate(code):
    with open("temp.c", "w") as f:
        f.write(code)

    cmd = f"Ultimate --core.toolchain.timeout.in.seconds 300 -tc AutomizerTermination.xml -s svcomp-Termination-64bit-Automizer_Default.epf -i temp.c"
    p = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, err = p.communicate()
    if err is not None:
        return output.decode(), err.decode()

    output = output.decode()
    return output, "No error"


def get_ground_truth(code):
    code = remove_hash_define(code)
    output = run_ultimate(code)

    return output


def main(file_name):
    input_file = file_name
    if not os.path.isfile(input_file):
        print("Input file does not exist")
        return -1

    fc_b = FramaCBenchmark(features="one_loop_one_method")

    input_data = None
    with open(input_file, "r") as f:
        input_files = f.read().splitlines()

    output_log = {}

    for i, benchmark in enumerate(input_files):
        print(
            f"{ACTION}{BOLD}[>]{END} {INFO}{BOLD}Processing benchmark {i+1}/{len(input_files)} | {benchmark} |{END}"
        )
        new_input_file = "../" + benchmark # We are one folder deeper in src/
        if not os.path.isfile(new_input_file):
            print(f"{FAIL}{BOLD}File {new_input_file} does not exist{END}")
            continue
        new_input = None
        with open(new_input_file, "r") as f:
            new_input = f.read()
        new_input = fc_b.preprocess(new_input, features="one_loop_one_method")
        output, error = get_ground_truth(new_input)
        benchmark_json = {"input": new_input, "output": output}
        if "RESULT: Ultimate proved your program to be correct!" in output:
            print(f"{SUCCESS}{BOLD}Proved benchmark {i+1}/{len(input_files)} | {END}")
            benchmark_json["result"] = "Proved"
        elif "RESULT: Ultimate proved your program to be incorrect!" in output:
            print(f"{FAIL}{BOLD}Disproved benchmark {i+1}/{len(input_files)} | {END}")
            benchmark_json["result"] = "Disproved"
        elif "RESULT: Ultimate could not prove your program: Timeout" in output:
            print(
                f"{WARNING}{BOLD}Timeout on benchmark {i+1}/{len(input_files)} | {END}"
            )
            benchmark_json["result"] = "Timeout"
        else:
            print(
                f"{FAIL}{BOLD}Unknown result on benchmark {i+1}/{len(input_files)} | {END}"
            )
            benchmark_json["result"] = "Unknown"
            print(output)

        output_log[new_input_file] = benchmark_json

    with open("output.json", "w", encoding="utf-8") as f:
        json.dump(output_log, f, ensure_ascii=False, indent=4)


if __name__ == "__main__":
    main(sys.argv[1])

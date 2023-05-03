import subprocess
import os

stats = {
    "SAT": 0,
    "UNSAT": 0,
    "TIMEOUT": 0,
    "ERROR": 0,
    "UNKNOWN": 0
}

z3_table = """| C Code | Z3 Status | Z3 Code | Z3 Output |
|--------|-----------|---------|-----------|
"""

def run_z3(smt_file: str, num: int):
    global z3_table
    if not os.path.exists(smt_file): return
    command = f"z3 {smt_file} -T:5"
    output = ""
    try:
        result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        # print("Z3 output:", result.stdout)
        output = f"STDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
        # return True
    except subprocess.CalledProcessError as e:
        # print("Error occurred:", e.stdout + "\n" + e.stderr)
        # breakpoint()
        output = f"STDOUT:\n{e.stdout}\n\nSTDERR:\n{e.stderr}"
        # return False
    finally:
        # with open("z3_output.txt", "a") as f:
        #     f.write(f"-------------------- {smt_file}\n")
        #     status = ""
        #     if "error" in output:
        #         if "unsat" in output:
        #             f.write("UNSAT")
        #             status = "UNSAT"
        #         else:
        #             f.write("ERROR")
        #             status = "ERROR"
        #     elif "sat" in output:
        #         f.write("SAT")
        #         status = "SAT"
        #     elif "timeout" in output:
        #         f.write("TIMEOUT")
        #         status = "TIMEOUT"
        #     else:
        #         f.write("UNKNOWN")
        #         status = "UNKNOWN"
        #     f.write("\n")
        #     f.write(output)
        status = ""
        if "error" in output:
            if "unsat" in output:
                status = "UNSAT"
            else:
                status = "ERROR"
        elif "sat" in output:
            status = "SAT"
        elif "timeout" in output:
            status = "TIMEOUT"
        else:
            status = "UNKNOWN"
        with open(f"z3/{i}.out", "w") as f2:
            f2.write(output)
        stats[status] += 1
        z3_table += f"| [{i}.c](./c_benchmark/{i}.c) | {status} | [{i}.smt2](./z3/{i}.smt2) | [{i}.out](./z3/{i}.out) |\n"

# # Example usage:
# smt_file = "path/to/your/input.smt"
# success = run_z3(smt_file)
# if success:
#     print("Z3 executed without errors.")
# else:
#     print("Z3 encountered an error.")

# Remove z3_output.txt if it exists
# if os.path.exists("z3_output.txt"):
#     os.remove("z3_output.txt")

if os.path.exists("z3_table.md"):
    os.remove("z3_table.md")

for i in range(1, 134):
    print(i)
    smt_file = f"z3/{i}.smt2"
    run_z3(smt_file, i)

with open("z3_table.md", "w") as f:
    f.write(f"""Overview of Z3 Results:
| Stat | Value |
|------|-------|
| Total No. of C Programs | 133 |
| SAT |{stats["SAT"]} |
| UNSAT | {stats["UNSAT"]} |
| TIMEOUT | {stats["TIMEOUT"]} |
| ERROR | {stats["ERROR"]} |
| UNKNOWN | {stats["UNKNOWN"]} |

{z3_table}
    """)

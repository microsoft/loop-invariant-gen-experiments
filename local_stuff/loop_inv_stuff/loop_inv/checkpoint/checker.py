import subprocess
import os

def run_z3(smt_file: str):
    command = f"z3 {smt_file} -T:5"
    output = ""
    try:
        result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        print("Z3 output:", result.stdout)
        output = result.stdout + result.stderr
        # return True
    except subprocess.CalledProcessError as e:
        print("Error occurred:", e.stdout + "\n" + e.stderr)
        # breakpoint()
        output = e.stdout + "\n" + e.stderr
        # return False
    finally:
        with open("z3_output.txt", "a") as f:
            f.write(f"-------------------- {smt_file}\n")
            if "error" in output:
                if "unsat" in output:
                    f.write("UNSAT")
                else:
                    f.write("ERROR")
            elif "sat" in output:
                f.write("SAT")
            elif "timeout" in output:
                f.write("TIMEOUT")
            else:
                f.write("UNKNOWN")
            f.write("\n")
            f.write(output)

# # Example usage:
# smt_file = "path/to/your/input.smt"
# success = run_z3(smt_file)
# if success:
#     print("Z3 executed without errors.")
# else:
#     print("Z3 encountered an error.")

# Remove z3_output.txt if it exists
if os.path.exists("z3_output.txt"):
    os.remove("z3_output.txt")

for i in range(1, 123):
    print(i)
    smt_file = f"bench/z3_output/{i}.smt2"
    run_z3(smt_file)
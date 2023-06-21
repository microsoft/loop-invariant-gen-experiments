import os
import subprocess

stats = {
    "PASS": 0,
    "FAIL": 0,
}

table = """| File | Z3 Status | SyGus | LLM Output | Z3 Checker | Checker Output |
|----- |-----------| ----- | ---------- | ---------- | -------------- |
"""

for file in os.listdir('z3_checkers'):
    try:
        result = subprocess.run([f"z3 z3_checkers/{file}"], shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        output = f"STDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
    except subprocess.CalledProcessError as e:
        output = f"STDOUT:\n{e.stdout}\n\nSTDERR:\n{e.stderr}"
    finally:
        status = "PASS" if "unsat" in output else "FAIL"
        stats[status] += 1
        with open(f"checker_output/{file[:-5]}.check", "w") as f:
            f.write(output)
        table += f"| {file} | {status} | [{file[:-5]}](xujie_code2inv/{file[:-5]}) | [{file[:-5]}.out](llm_output/{file[:-5]}.out) | [{file[:-5]}.smt2](z3_checkers/{file[:-5]}.smt2) | [{file[:-5]}.check](checker_output/{file[:-5]}.check)\n"
        
if os.path.exists("table.md"):
    os.remove("table.md")

with open("table.md", "w") as f:
     f.write(f"""Overview of Results:
| Stat | Value |
|------|-------|
| Total | {len(os.listdir("z3_checkers"))} |
| PASS | {stats["PASS"]} |
| FAIL | {stats["FAIL"]} |

{table}
    """)
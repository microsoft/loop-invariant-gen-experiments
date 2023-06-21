import subprocess
import os

stats = {
    "Verified": 0,
    "Error": 0,
}

boogie_table = """| C Code | Boogie Status | Boogie Code | Boogie Output |
|--------|---------------|-------------|---------------|
"""

dir = "boogie"

def run_boogie(boogie_file: str, num: int):
    global boogie_table
    if not os.path.exists(boogie_file): return
    command = f"boogie {boogie_file}"
    output = ""
    try:
        result = subprocess.run(command, shell=True, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        output = f"STDOUT:\n{result.stdout}\n\nSTDERR:\n{result.stderr}"
    except subprocess.CalledProcessError as e:
        output = f"STDOUT:\n{e.stdout}\n\nSTDERR:\n{e.stderr}"
    finally:
        status = ""
        if "1 verified" in output:
            status = "Verified"
        else:
            status = "Error"
        with open(f"{dir}/{i}.out", "w") as f2:
            f2.write(output)
        stats[status] += 1
        boogie_table += f"| [{i}.c](./c_benchmark_anon/{i}.c) | {status} | [{i}.bpl](./boogie/{i}.bpl) | [{i}.out](./boogie/{i}.out) |\n"


if os.path.exists(f"{dir}_table.md"):
    os.remove(f"{dir}_table.md")


# tot = len(os.listdir(dir))
tot = 133
for i in range(1, tot+1):
    print(i)
    boogie_file = f"{dir}/{i}.bpl"
    run_boogie(boogie_file, i)

with open(f"{dir}_table.md", "w") as f:
    f.write(f"""Overview of Boogie Results:
| Stat | Value |
|------|-------|
| Total No. of C Programs | 133 |
| Verified | {stats["Verified"]} |
| Error | {stats["Error"]} |

{boogie_table}
    """)

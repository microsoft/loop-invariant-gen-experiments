import os

for file in os.listdir("boogie_translated"):
    invariants = []
    with open(f"boogie_llm/{file}") as f:
        text = f.read()
        lines = text.splitlines()
        for line in lines:
            if "invariant" in line:
                line = line.replace("%", "mod")
                invariants.append(line.strip())
    with open(f"boogie_translated/{file}") as f:
        text = f.read()
        lines = text.splitlines()
        loc = None
        for index, line in enumerate(lines):
            if "insert invariants" in line:
                loc = index
                break
        if loc is not None:
            lines = lines[:loc+1] + invariants + lines[loc+1:]
        else:
            raise Exception("No insert invariants found")
        with open(f"boogie_translated/{file}", "w") as f:
            f.write('\n'.join(lines))
        
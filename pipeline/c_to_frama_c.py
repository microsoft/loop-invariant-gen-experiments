import os
import re

count = 0
for file in os.listdir("c_benchmarks/code2inv/"):
    if file.endswith(".c"):
        with open("c_benchmarks/code2inv/" + file, "r") as f:
            code = f.read()
            new_code = ""
            for i, codeline in enumerate(code.splitlines()):
                if "assert" in codeline and not "//assert" in codeline:
                    assertion = codeline.strip()
                    codeline = codeline.replace(
                        assertion, "{;\n //@ " + assertion + "\n}"
                    )
                    count += 1
                new_code += codeline + "\n"
            new_code = """#define assume(e) if(!(e)) return 0;
extern int unknown(void);

""" + "".join(
                new_code
            )
            with open("c_benchmarks/frama_c_code2inv/" + file, "w") as fi:
                fi.write(new_code)


def transform_code(self, code):
    lines = code.splitlines()
    new_code = ""
    for line in lines:
        if "assert" in line and not "//assert" in line:
            assertion = line.strip()
            line = line.replace(assertion, "{;\n //@ " + assertion + "\n}")
        new_code += line + "\n"
    new_code = (
        """#define assume(e) if(!(e)) return 0;\nextern int unknown(void);\n"""
        + "".join(new_code)
    )
    return new_code

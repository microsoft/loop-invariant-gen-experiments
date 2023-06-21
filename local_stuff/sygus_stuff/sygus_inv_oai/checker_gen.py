import os
import re

tot = len(os.listdir("xujie_code2inv"))

# breakpoint()

for file_num, file in enumerate(os.listdir("xujie_code2inv")):
    output = "(set-logic LIA)\n\n"
    with open(f"llm_output/{file}.out", "r") as f:
        output += f.read()
        output += "\n\n"

    with open(f"xujie_code2inv/{file}", "r") as f:
        lines = f.readlines()
        start = -1
        end = -1
        num_args = -1
        for i, line in enumerate(lines):
            if line.startswith("(synth-inv"):
                matches = re.findall(r'\bInt\b', line)
                num_args = len(matches)
                start = i
                continue
            elif line.startswith("(inv-constraint"):
                end = i
                break

        if start != -1 and end != -1 and num_args != -1:
            output += "\n".join(lines[start+1:end])
            output += "\n\n"

            declare_vars = ""
            v_vars = ""
            v_prime_vars = ""

            for i in range(num_args):
                declare_vars += f"(declare-const v{i} Int)\n"
                declare_vars += f"(declare-const v{i}! Int)\n"
                v_vars += f"v{i} "
                v_prime_vars += f"v{i}! "

            inv_constraint = f"""
{declare_vars}
(assert
    (or
        (not (=> 
            (pre-f {v_vars}) 
            (inv-f {v_vars})
        ))


        (not (=>
            (and 
                (inv-f {v_vars})
                (trans-f {v_vars} {v_prime_vars})
            )
            (inv-f {v_prime_vars})
        ))


        (not (=> 
            (inv-f {v_vars}) 
            (post-f {v_vars})
        ))
    )
)

(check-sat)
                """
            output += inv_constraint
            
            with open(f"z3_checkers/{file}.smt2", "w") as f:
                f.write(output)

            print(f"Done with {file} - {file_num}/{tot}")
        else:
            print(f"Error in {file} - {file_num}/{tot}")
            break
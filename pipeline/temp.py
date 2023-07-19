import os

for file in os.listdir('../code2inv/'):
    if file.endswith('.c'):
        with open('../code2inv/' + file, 'r') as f:
            code = f.read()
            new_code = ''
            for line in code.splitlines():
                if 'assert' in line:
                    new_code += line.replace('assert', '//@ assert') + '\n'
                else:
                    new_code += line + '\n'
            with open(file, 'w') as fi:
                fi.write(new_code)

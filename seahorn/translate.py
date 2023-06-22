import re

def initialize_variables(filename):
    with open(filename, 'r') as file:
        data = file.read()
        
    main_start = data.find('int main()')
    main_end = data.find('}', main_start)

    main_body = data[main_start:main_end]
    lines = main_body.split('\n')

    new_lines = []
    for line in lines:
        match = re.match(r'\s*int (\w+(?:,\s*\w+)*);', line)
        if match:
            vars_str = match.group(1)
            vars_list = [var.strip() for var in vars_str.split(',')]
            for var in vars_list:
                new_line = f'int {var} = unknown();'
                new_lines.append(new_line)
        else:
            new_lines.append(line)

    new_main_body = '\n'.join(new_lines)
    new_data = data[:main_start] + new_main_body + data[main_end:]
    
    with open(filename, 'w') as file:
        file.write(new_data)

# usage
import os
for file in os.listdir("seahorn_benchmark"):
    initialize_variables(f'seahorn_benchmark/{file}')


with open('table.md') as f:
    lines = f.readlines()
    for line in lines:
        if ' | PASS' in line:
            name = line.split('|')[1].strip()[:-7]+'out'
            print(name)
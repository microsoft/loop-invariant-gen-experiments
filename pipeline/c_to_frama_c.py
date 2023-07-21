import os

for file in os.listdir('c_benchmarks/code2inv/'):
    if file.endswith('.c'):
        with open('c_benchmarks/code2inv/' + file, 'r') as f:
            code = f.read()
            new_code = """#define assume(e) if(!(e)) return 0;
#define assert(e) "{; //@ assert(" #e ")}"
extern int unknown(void);

""" + code
            with open('c_benchmarks/frama_c_code2inv/' + file, 'w') as fi:
                fi.write(new_code)

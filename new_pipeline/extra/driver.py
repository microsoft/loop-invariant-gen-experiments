import sys
sys.path.append('../')

import frama_c

if len(sys.argv) < 3:
    print("Usage: driver <c-file> <llm_out> [invarinat|variant]")

print("Program file: ", sys.argv[1])
print("Invariant file: ", sys.argv[2])
checker = frama_c.FramaCChecker()
bench = frama_c.FramaCBenchmark()

with open(sys.argv[1], "r") as f, open(sys.argv[2], "r") as llm_out:
    input_code = f.read()
    llm_outputs = llm_out.read()
    checker_input, loop_list = bench.preprocess(input_code)
#    checker_input = bench.raw_input_to_checker_input(preprocessed_input)
    inv_code = bench.combine_llm_outputs(checker_input, [llm_outputs], sys.argv[3])
    success, inv = checker.prune_annotations_and_check(inv_code, sys.argv[3], True)

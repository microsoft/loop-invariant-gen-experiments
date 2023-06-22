- accelerating_inv_gen
    [x] cav
    [x] dagger
    [x] invgen
    [x] svcomp


- parser has to accomodate arrays
- no for loops allowed

Observations:
- had to change for loops to while, function inlining, eliminating goto statements, inserting unknown() (appears as nondet_int(), __BLAST_NONDET var, etc.) etc.
- the parser written is for the code2inv benchmark which follows a consistent pattern. seeing 1 file is the same as having seen all. The loop-invgen benchmark is not consistent even within a single source. It seems like it was assembled from very diverse sets of benchmarks. Therefore, it is best to go through each file and incrementally add functionality to the parser+codegen as necessary.

Process:
- C-to-C_subset manual translation
- filter out multiple loops
- parser+codegen - need to incrementally add functionality by attempting to parse a significant subset of files

Meeting Notes:
- Take subset that looks like code2inv and implement parser functionality.


New Start:
[x] convert while(1), assert(0), assert(1) to while(true)
[x] separate unknown() into unknown() and unknown_int()
[x] remove unsigned from translated code
[x] create checker that will remove asserts and check for syntactic correctness
    - parse (error?)
    - remove asserts
    - write to /tmp/
    - invoke boogie (error?)
    - write to file in parallel directory structure

Task 1:
- Characterize the benchmark sources with readmes in each folder => table (grep)
    - pointer
    - array
    - loops
    - functions
        - top-level curly braces = check if there are tools that do it

- add benchmark source for CHC solver
- collate all benchmark tables - universal data

Task 2: Frama-C

Task 3:
- Documenting Code
- Documenting Results
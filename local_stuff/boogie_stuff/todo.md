Done:
- diversity of invgen
Diversity of unique invariants generated for 3 completions:

Number of completions for Invariant Generation: 3
1 Unique Invariants: 14 files
2 Unique Invariants: 46 files
3 Unique Invariants: 27 files
4 Unique Invariants: 23 files
5 Unique Invariants: 10 files
6 Unique Invariants: 8 files
7 Unique Invariants: 3 files
9 Unique Invariants: 1 files
11 Unique Invariants: 1 files
Average # Unique Invariants: 3.142857142857143

- num retries = 15
   - +6

Observations:
dynaroars/dig - vtrace unclear, doesn't have ground truth postconditions - meant to generate loop invariants at arbitrary program locations
SaswatPadhi/LoopInvGen:
- Polyrank - doesn't have c benchmarks (has .loop benchmarks)
- Hola - Broken link, paper doesn't point to benchmark link + no github page
- *Accelerating Invariant Generation* - Has C benchmarks
- *PILAT* - has C benchmark but non-linear
- Sygus-Comp - doesn't have C benchmarks. Only .sl files
- FiB - doesn't have C benchmarks. Only .impp files
- code2inv - already using
- *SV-Comp* - Has C benchmarks

Its best to manually translate the C files to Boogie due to the diversity and idiosyncrasies of each benchmark. Set aside NIA, arrays, etc. for now and focus on converting LIA benchmarks to boogie. If there isn't enough of that, continue on to NIA.

Use Boogie Lang Ref publication found.

TODO:
- sampling experiment - n = 1, 2, 3
- bug in partitioning logic - see pipeline/test.bpl
- finally analyze failed LLM cases over teams chat/meeting
- boogie command error in VM
- partitioning - comment asserts
- collect c benchmarks from different source (first collect, then translate, maintain mapping/links)
    - requirements - 1 function (int main), precond - assume, postcond - assert, one loop
    - maintain lineage/mapping of converted files to original benchmarks
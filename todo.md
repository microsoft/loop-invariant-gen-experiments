# Progress

## Done

- (Checker + prompt sequence)-parametric pipeline
- Added new benchmarks for array reasoning
- Report Code2Inv numbers using new pipeline without healing

## TODO

- Run healing on Code2Inv
- Merge `adharsh/new-pipeline` into `main`
- Try simplified prompt sequence (don't do 3+ back-and-forth with the model; just one prompt)
- Make the "library" of prompt lines to be used with the simplified sequence
- Run `seahorn` for `new_benchmarks`
- Write the `transform` function for `new_benchmarks`

## Plan (Day 0: Wednesday, 26th July)
- healing
    - simplify healing prompts - do Thu morning (Adharsh)
    - run the code2inv that need healing - schedule Thu evening
- run new benchmarks with only 1 loop
    - phase 1: no healing (phase1-success) - now Wed
    - phase 2: needs healing (phase1-fails) - schedule Fri
- add "nudges"
    - design nudges - do Thu morning (Subhajit)
    - rerun phase1-fails -- tentative Thu evening
- array program
    - deisgn prompts - do Friday (both)
    - implement in framework - do Friday (Adharsh)
    - design nudges - do Friday (Subhajit)
    - run diffy benchmarks - schedule Monday 
- termination benchamrks
    - add benchmarks (https://termination-portal.org/wiki/Termination\_Competition\_2022)
    - deisgn prompts - do Monday (both)
    - implement in framework - do Monday (Adharsh)
    - design nudges - do Monday (Subhajit)
    - run diffy benchmarks - schedule Tuesday 
- remove faulty benchmarks
    - run with seahorn and other verfiers to remove instances that are buggy/non-terminating


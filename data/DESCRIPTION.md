# Features of the original benchmarks

## 1. accelerating_invariant_generation

Has 5 subdirectories which have distinct features:

### cav
- Uses `unknown1, unknown2, unknown3, unknown4`
- Post-condition is in the format `if( CONDITION ) { goto ERROR; ERROR:; }`

### crafted
- No `unknown`s
- Uses a `__VERIFIER_assert` defined in `myassert.h`

### dagger
- Uses `nondet_int`
- Uses a `__VERIFIER_assert` defined in `myassert.h`
- Preconditions are encoded as `if( !CONDITION ) return;`

### invgen
- Uses `assume` for precondition
- Uses a `tmpl` function (TODO)
- Uses a `__VERIFIER_assert` defined in `myassert.h`

### svcomp
- Uses `__VERIFIER_nondet_int, __VERIFIER_nondet_uint, __VERIFIER_nondet_char, __VERIFIER_nondet_bool` for unknowns
- Uses `__VERIFIER_assume` for pre-condition
- Uses `__VERIFIER_assert` for post-condition
- All of these are either `extern` of defined in the same file

## 2. diffy_cav21_bench

- Has 2 subdirectories
- Uses `__VERIFIER_nondet_int` for unknowns
- Uses `__VERIFIER_assume` for pre-condition
- Uses `__VERIFIER_assert` for post-condition

## 3. LinearArbitrary-SeaHorn

- All are in seahorn-compatible format already

## 4. non_termination

- Has 2 subdirectories which have distinct features.
- Uses `__VERIFIER_nondet_int, __VERIFIER_nondet_uint, __VERIFIER_nondet_ushort` for unknowns
- No assertions because these are non-termination benchmarks

## 5. pilat

- 20 benchmarks
- Uses `pre, post, inv` for pre-condition, post-condition, and invariant respectively
- `pre` and `post` will have to be converted to other formats for ground-truth and even for Frama-C.

## 6. sv-benchmarks

- Has 12 subdirectories which have distinct features.
- Uses `__VERIFIER_assert` for post-condition.
- uses `__VERIFIER_nondet_int, __VERIFIER_nondet_uint, __VERIFIER_nondet_char, __VERIFIER_nondet_bool` for unknowns
- Use `assume_abort_if_not` for pre-conditions

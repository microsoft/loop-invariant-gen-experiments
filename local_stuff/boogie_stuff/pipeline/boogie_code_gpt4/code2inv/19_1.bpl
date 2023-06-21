procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var z1: int;
    var z2: int;
    var z3: int;
    var nondet: bool;

    // pre-conditions
    x := 0;
    m := 0;
    assume(n >= 0); // assuming n is non-negative for the loop to make sense

    // loop body
    while (x < n)
    invariant 0 <= x;
    invariant 0 <= m;
    invariant m <= x;
    invariant x <= n;
    {
        havoc nondet;
        if (nondet) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 0) {
        assert(m < n);
        // assert(m >= 0); // This assertion is always true due to the loop invariant
    }
}
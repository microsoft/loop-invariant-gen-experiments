procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    x := 0;
    m := 0;

    // loop body
    while (x < n)
    invariant 0 <= x <= n;
    invariant 0 <= m <= x;
    {
        havoc nondet;
        if (nondet) {
            m := x;
        }
        x := x + 1;
    }

    // post-condition
    if (n > 0) {
        assert(m >= 0);
        // assert(m < n); // commented out in the original C code
    }
}
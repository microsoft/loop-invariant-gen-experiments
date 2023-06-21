procedure main()
{
    var n: int;
    var c: int;
    var nondet: bool;

    // pre-conditions
    assume(n > 0);

    // loop body
    while (nondet)
    invariant 1 <= c;
    invariant c <= n;
    {
        havoc nondet;
        if (c == n) {
            c := 1;
        }
        else {
            c := c + 1;
        }
    }

    // post-condition
    if (c == n) {
        assert(c >= 0);
        // assert(c <= n); // This assertion is commented out in the original C code
    }
}
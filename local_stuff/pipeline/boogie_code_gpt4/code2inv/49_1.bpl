procedure main()
{
    var c: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    assume(n > 0);
    c := 0;

    // loop body
    while (nondet)
    invariant n > 0;
    invariant c >= 0;
    invariant c <= n;
    {
        havoc nondet;
        if (nondet) {
            if (c != n) {
                c := c + 1;
            }
        } else {
            if (c == n) {
                c := 1;
            }
        }
    }

    // post-condition
    if (n <= -1) {
        assert(c != n);
    }
}
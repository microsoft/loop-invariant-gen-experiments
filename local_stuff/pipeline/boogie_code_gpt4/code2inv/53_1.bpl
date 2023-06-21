procedure main()
{
    var c: int;
    var n: int;
    var v1: int;
    var v2: int;
    var v3: int;
    var nondet: bool;

    // pre-conditions
    c := 0;
    assume(n > 0);

    // loop body
    while (nondet)
    invariant c >= 0;
    invariant c <= n + 1;
    {
        havoc nondet;
        if (nondet) {
            if (c > n) {
                c := c + 1;
            }
        } else {
            if (c == n) {
                c := 1;
            }
        }
    }

    // post-condition
    if (c != n) {
        assert(c >= 0);
    }
}
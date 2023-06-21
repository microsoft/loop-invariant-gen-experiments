procedure main()
{
    var c: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    c := 0;
    assume(n > 0);

    // loop body
    while (nondet)
    invariant 0 <= c;
    invariant c <= n;
    {
        havoc nondet;
        if (nondet && (c != n)) {
            c := c + 1;
        } else if (!nondet && (c == n)) {
            c := 1;
        }
    }

    // post-condition
    if (c < 0) {
        if (c > n) {
            assert(c == n);
        }
    }
}
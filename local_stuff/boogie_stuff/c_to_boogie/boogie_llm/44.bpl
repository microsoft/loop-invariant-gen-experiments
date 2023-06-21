procedure main()
{
    var c: int;
    var n: int;
    var nondet1: bool;
    var nondet2: bool;

    // pre-conditions
    c := 0;
    assume(n > 0);

    // loop body
    while (true)
    invariant c >= 0;
    invariant c <= n + 1;
    {
        havoc nondet1;
        if (nondet1) {
            if (c > n) {
                c := c + 1;
            }
        } else {
            havoc nondet2;
            if (nondet2) {
                if (c == n) {
                    c := 1;
                }
            }
        }
    }

    // post-condition
    if (n <= -1) {
        assert(c != n);
    }
}
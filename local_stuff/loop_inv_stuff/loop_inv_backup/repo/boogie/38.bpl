 procedure main()
    {
        var n: int;
        var c: int;
        var nondet: bool;
        assume(n > 0);
        c := 0;
        // loop body
        havoc nondet;
        while (nondet)
        invariant c >= 0 && c <= n;
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
            //assert(c <= n);
        }
    }
 procedure main()
    {
        var n: int;
        var c: int;
        var nondet: bool;
        assume(n > 0);
        c := 0;
        havoc nondet;
        while (nondet)
            invariant 0 <= c && c <= n;
        {
            if (c == n) {
                c := 1;
            } else {
                c := c + 1;
            }
            havoc nondet;
        }
        if (c == n) {
            assert(c <= n);
        }
    }
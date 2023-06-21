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
        while (*)
        invariant c >= 0;
        invariant c <= n;
        {
            havoc nondet1;
            havoc nondet2;
            if (nondet1) {
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
        if (c < 0 || c > n) {
            assert(c == n);
        }
    }
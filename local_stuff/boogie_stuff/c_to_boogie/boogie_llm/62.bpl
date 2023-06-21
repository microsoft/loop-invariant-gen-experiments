procedure main()
    {
        var c: int;
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var nondet: bool;
        var nondet2: bool;

        // pre-conditions
        c := 0;
        assume(n > 0);

        // loop body
        while (true)
        invariant 0 <= c && c <= n;
        invariant c == n || c != n;
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

            // break condition
            havoc nondet2;
            if (nondet2) {
                break;
            }
        }

        // post-condition
        if (n > -1) {
            assert(c == n);
        }
    }
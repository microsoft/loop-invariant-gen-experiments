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
        invariant c >= 0;
        invariant c <= n + 1;
        {
            havoc nondet;
            havoc nondet2;
            if (nondet) {
                if (c > n) {
                    c := c + 1;
                }
            } else {
                if (c == n) {
                    c := 1;
                }
            }

            if (!nondet2) {
                break;
            }
        }

        // post-condition
        if (n > -1) {
            assert(c != n);
        }
    }
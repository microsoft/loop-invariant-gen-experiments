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
        invariant c >= 0 && c <= n;
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

            if (!nondet2) {
                break;
            }
        }

        // post-condition
        if (c != n) {
            assert(c >= 0);
        }
    }
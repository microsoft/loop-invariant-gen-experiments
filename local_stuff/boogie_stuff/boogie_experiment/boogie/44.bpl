procedure main()
    {
        var x1: int;
        var x2: int;
        var nondet1: bool;
        var nondet2: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 > 0);

        // loop body
        while (true)
        invariant x1 >= 0;
        invariant x2 > 0;
        invariant (x1 != x2) || (x1 == 0 && x2 > 0);
        {
            havoc nondet1;
            havoc nondet2;
            if (nondet1) {
                if (x1 > x2) {
                    x1 := x1 + 1;
                }
            } else {
                if (x1 == x2) {
                    x1 := 1;
                }
            }

            if (!nondet2) {
                break;
            }
        }

        // post-condition
        if (x2 <= -1) {
            assert(x1 != x2);
        }
    }
procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var nondet1: bool;
        var nondet2: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 > 0);

        // loop body
        while (*)
        invariant x1 >= 0;
        invariant x2 > 0;
        invariant x1 == x2 || x1 != x2;
        {
            havoc nondet1;
            if (nondet1) {
                if (x1 != x2) {
                    x1 := x1 + 1;
                }
            } else {
                havoc nondet2;
                if (nondet2) {
                    if (x1 == x2) {
                        x1 := 1;
                    }
                }
            }
        }

        // post-condition
        if (x2 > -1) {
            assert(x1 != x2);
        }
    }
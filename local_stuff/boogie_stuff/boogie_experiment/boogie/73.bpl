procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var nondet: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 >= 0);
        assume(x2 >= 127);
        x3 := 36 * x2;

        // loop body
        while (nondet)
        invariant x1 >= 0;
        invariant x3 >= 36 * x1;
        {
            havoc nondet;
            if (x1 < 36) {
                x3 := x3 + 1;
                x1 := x1 + 1;
            }
        }

        // post-condition
        if (x3 < 0) {
            if (x3 >= 4608) {
                assert(x1 >= 36);
            }
        }
    }
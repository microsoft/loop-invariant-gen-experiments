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
        invariant x1 <= 36;
        invariant x3 >= 36 * x2;
        invariant x3 <= 36 * x2 + x1;
        invariant x1 == 0 || x1 == 36 || x3 < 4608;
        {
            havoc nondet;
            if (x1 < 36) {
                x3 := x3 + 1;
                x1 := x1 + 1;
            }
        }

        // post-condition
        if (x1 < 36) {
            assert(x3 < 4608);
        }
    }
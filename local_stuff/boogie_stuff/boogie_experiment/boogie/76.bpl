procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;
        var nondet: bool;

        // pre-conditions
        x1 := 0;
        assume(x5 >= 0);
        assume(x5 >= 127);
        x6 := (36 * x5);

        // loop body
        while (nondet)
        invariant x1 >= 0;
        invariant x6 >= 36 * x1;
        {
            havoc nondet;
            if (x1 < 36) {
                x6 := (x6 + 1);
                x1 := (x1 + 1);
            }
        }

        // post-condition
        if (x6 < 0) {
            if (x6 >= 4608) {
                assert(x1 >= 36);
            }
        }
    }
procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var nondet: bool;

        // pre-condition
        x1 := 1;
        x2 := 1;

        // loop body
        while (x1 < x3)
        invariant x1 >= 1;
        invariant 1 <= x2 && x2 <= x1;
        invariant x1 == 1 || x2 < x3;
        {
            havoc nondet;
            if (nondet) {
                x2 := x1;
            }
            x1 := x1 + 1;
        }

        // post-condition
        if (x3 > 1) {
            assert (x2 < x3);
        }
    }
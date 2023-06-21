procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;
        var nondet: bool;

        // pre-condition
        x4 := 1;
        x5 := 1;

        // loop body
        while (x4 < x6)
        invariant x4 >= 1;
        invariant 1 <= x5 && x5 <= x4;
        {
            havoc nondet;
            if (nondet) {
                x5 := x4;
            }
            x4 := x4 + 1;
        }

        // post-condition
        if (x6 > 1) {
            assert (x5 >= 1);
        }
    }
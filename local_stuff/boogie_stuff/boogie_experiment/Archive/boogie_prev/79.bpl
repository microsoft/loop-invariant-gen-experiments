procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var nondet: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 >= 0);
        assume(x3 >= 0);
        assume(x2 >= x3);

        // loop body
        while (nondet)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && (x1' = x1 + 1 || x1' = x1) => x1' >= 0
        invariant x1 <= x2; // 1) x1 = 0 && x2 >= 0 => x1 <= x2, 2) x1 <= x2 && (x1' = x1 + 1 || x1' = x1) => x1' <= x2
        invariant x1 >= x3 || x1 < x3; // 1) x1 = 0 => x1 >= x3 || x1 < x3, 2) (x1 >= x3 || x1 < x3) && (x1' = x1 + 1 || x1' = x1) => x1' >= x3 || x1' < x3
        {
            havoc nondet;
            if (x1 < x3)
            {
                x1 := x1 + 1;
            }
        }

        // post-condition
        if (x1 >= x2)
        {
            if (0 > x1)
            {
                assert(x1 >= x3);
            }
        }
    }
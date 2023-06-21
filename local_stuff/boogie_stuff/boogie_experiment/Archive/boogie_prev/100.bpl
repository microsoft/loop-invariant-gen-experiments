procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-conditions
        assume(x1 >= 0);
        x2 := x1;
        x3 := 0;

        // loop body
        while (x2 > 0)
        invariant x2 >= 0; // 1) x2 = x1 => x2 >= 0, 2) x2 >= 0 && x2' = x2 - 1 => x2' >= 0
        invariant x3 >= 0; // 1) x3 = 0 => x3 >= 0, 2) x3 >= 0 && x3' = x3 + 1 => x3' >= 0
        invariant x1 == x2 + x3; // 1) x1 = x2, x3 = 0 => x1 = x2 + x3, 2) x1 = x2 + x3 && x2' = x2 - 1 && x3' = x3 + 1 => x1 = x2' + x3'
        {
            x3 := x3 + 1;
            x2 := x2 - 1;
        }

        // post-condition
        assert(x3 == x1);
    }
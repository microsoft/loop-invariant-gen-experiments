procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;

        // pre-conditions
        assume(x3 >= 0);
        assume(x4 >= 0);
        x1 := 0;
        x2 := 0;

        // loop body
        while (x1 <= x4)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && x1' = x1 + 1 => x1' >= 0
        invariant x2 >= 0; // 1) x2 = 0 => x2 >= 0, 2) x2 >= 0 && x2' = x2 + x1 + 1 => x2' >= 0
        invariant x1 * (x1 + 1) / 2 <= x2; // 1) x1 = 0 => x1 * (x1 + 1) / 2 <= x2, 2) x1 * (x1 + 1) / 2 <= x2 && x2' = x2 + x1 + 1 => x1' * (x1' + 1) / 2 <= x2'
        {
            x1 := x1 + 1;
            x2 := x2 + x1;
        }

        // post-condition
        assert((x1 + (x2 + x3)) > (2 * x4));
    }
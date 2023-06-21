procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-condition
        x3 := 0;
        x1 := 1;

        // loop body
        while (x1 <= x2)
        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 1 => x1' >= 1
        invariant x3 >= 0; // 1) x3 = 0 => x3 >= 0, 2) x3 >= 0 && x3' = x3 + 1 => x3' >= 0
        invariant x3 == x1 - 1; // 1) x3 = 0, x1 = 1 => x3 == x1 - 1, 2) x3 == x1 - 1 && x1' = x1 + 1 && x3' = x3 + 1 => x3' == x1' - 1
        {
            x1 := x1 + 1;
            x3 := x3 + 1;
        }

        // post-condition
        if (x3 != x2) {
            assert (x3 == x1 - 1);
        }
    }
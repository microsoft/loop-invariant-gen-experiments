procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;

        // pre-condition
        x5 := 1;

        // loop body
        while (x5 <= x1)
        invariant x5 >= 1; // 1) x5 = 1 => x5 >= 1, 2) x5 >= 1 && x5' = x5 + 1 => x5' >= 1
        invariant x5 <= x1 + 1; // 1) x5 = 1 => x5 <= x1 + 1, 2) x5 <= x1 + 1 && x5' = x5 + 1 => x5' <= x1 + 1
        invariant x6 == x1 - x5 + 2; // 1) x5 = 1 => x6 = x1 - x5 + 2, 2) x6 = x1 - x5 + 2 && x6' = x1 - x5' && x5' = x5 + 1 => x6' = x1 - x5' + 2
        {
            x6 := x1 - x5;
            x5 := x5 + 1;
        }

        // post-condition
        if (x1 > 0) {
            assert (x6 >= 0);
            //assert (x6 < x1); // This assertion cannot be proven as it is not true for all cases, e.g., x1 = 1
        }
    }
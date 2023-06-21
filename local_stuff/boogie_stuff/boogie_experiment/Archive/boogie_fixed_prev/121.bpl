procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x2 := 0;
        x1 := 1;

        // loop body
        while (x1 <= 8)
        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 1 => x1' >= 1
        invariant x2 >= 0; // 1) x2 = 0 => x2 >= 0, 2) x2 >= 0 && x2' = x2 + 1 => x2' >= 0
        invariant x1 - x2 == 1; // 1) x1 = 1, x2 = 0 => x1 - x2 == 1, 2) x1 - x2 == 1 && x1' = x1 + 1 && x2' = x2 + 1 => x1' - x2' == 1
        {
            x1 := x1 + 1;
            x2 := x2 + 1;
        }

        // post-condition
        if (x2 != 0) {
            assert (x1 - x2 == 1);
        }
    }
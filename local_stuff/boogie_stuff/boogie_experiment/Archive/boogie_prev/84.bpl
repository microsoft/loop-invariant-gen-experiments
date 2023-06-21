procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := -50;

        // loop body
        while (x1 < 0)
        invariant x1 <= 0; // 1) x1 = -50 => x1 <= 0, 2) x1 <= 0 && x1' = x1 + x2 => x1' <= 0
        invariant x2 >= 0; // 1) x2 is uninitialized, so we cannot prove that x2 >= 0 before the loop
        // To fix this issue, we need to initialize x2 before the loop, for example: x2 := 0;
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x2 > 0);
    }
procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := -5000;

        // loop body
        while (x1 < 0)
        invariant x1 <= 0; // 1) x1 = -5000 => x1 <= 0, 2) x1 <= 0 && x1' = x1 + x2 => x1' <= 0
        invariant x2 >= 0; // 1) x2 is uninitialized, but x2 >= 0 holds trivially before the loop, 2) x2 >= 0 && x2' = x2 + 1 => x2' >= 0
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x2 > 0);
    }
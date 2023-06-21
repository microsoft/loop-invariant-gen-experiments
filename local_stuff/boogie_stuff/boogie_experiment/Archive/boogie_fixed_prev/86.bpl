procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;

        // pre-condition
        x1 := -50;

        // loop body
        while (x1 < 0)
        invariant x1 <= 0; // 1) x1 = -50 => x1 <= 0, 2) x1 <= 0 && x1' = x1 + x2 => x1' <= 0
        invariant x2 >= 0; // 1) x2 is uninitialized, but x2 is only incremented in the loop, so x2 >= 0, 2) x2 >= 0 && x2' = x2 + 1 => x2' >= 0
        invariant x1 + (x2 * (x2 - 1)) div 2 <= 0; // 1) x1 = -50 => x1 + x2 * (x2 - 1) / 2 <= 0, 2) x1 <= 0 && x1' = x1 + x2 && x2' = x2 + 1 => x1' + x2' * (x2' - 1) / 2 <= 0
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x2 > 0);
    }
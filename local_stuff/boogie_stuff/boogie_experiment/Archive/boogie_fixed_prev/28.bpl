procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x2 := x1;

        // loop body
        while (x2 > 0)
        invariant x2 >= 0; // 1) x2 = x1 => x2 >= 0 (since x2 > 0), 2) x2 >= 0 && x2' = x2 - 1 => x2' >= 0
        invariant x2 <= x1; // 1) x2 = x1 => x2 <= x1, 2) x2 <= x1 && x2' = x2 - 1 => x2' <= x1
        invariant x1 >= 0; // 1) x2 = x1 => x1 >= 0 (since x2 > 0), 2) x1 >= 0 && x2' = x2 - 1 => x1' >= 0
        {
            x2 := x2 - 1;
        }

        // post-condition
        if (x2 != 0) {
            assert (x1 < 0);
        }
    }
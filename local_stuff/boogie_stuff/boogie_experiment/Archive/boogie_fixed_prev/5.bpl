procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;

        // pre-condition
        x1 := 0;

        // loop body
        while (x1 < x2)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >=0 && x1' = x1 + 1 => x1' >= 0
        invariant x1 <= x2; // 1) x1 = 0 => x1 <= x2, 2) x1 <= x2 && x1' = x1 + 1 => x1' <= x2
        invariant x1 == 0 || x4 >= x3;
        {
            x1 := x1 + 1;
            if (x4 <= x3) {
                x3 := x4;
            }
        }

        // post-condition
        if (x2 > 0) {
            assert (x4 >= x3);
        }
    }
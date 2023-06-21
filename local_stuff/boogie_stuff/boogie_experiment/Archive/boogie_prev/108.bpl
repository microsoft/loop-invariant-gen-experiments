procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;

        // pre-condition
        assume(x1 <= x3);
        x4 := 0;
        x5 := 0;

        // loop body
        while (x5 < x2)
        invariant x5 >= 0; // 1) x5 = 0 => x5 >= 0, 2) x5 >= 0 && x5' = x5 + 1 => x5' >= 0
        invariant x5 <= x2; // 1) x5 = 0 => x5 <= x2, 2) x5 <= x2 && x5' = x5 + 1 => x5' <= x2
        invariant x1 <= x3; // 1) x1 <= x3 => x1 <= x3, 2) x1 <= x3 && (x3' = x1 || x3' = x3) => x1 <= x3'
        {
            if (x3 < x1) {
                x3 := x1;
            }
            x5 := x5 + 1;
        }

        // post-condition
        assert(x1 <= x3);
    }
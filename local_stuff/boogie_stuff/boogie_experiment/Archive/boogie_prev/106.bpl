procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;

        // pre-condition
        assume(x1 <= x2);
        assume(x3 < 1);
        x4 := 0;

        // loop body
        while (x4 < 1)
        invariant x4 >= 0; // 1) x4 = 0 => x4 >= 0, 2) x4 >=0 && x4' = x4 + 1 => x4' >= 0
        invariant x4 <= 1; // 1) x4 = 0 => x4 <= 1, 2) x4 <= 1 && x4' = x4 + 1 => x4' <= 1
        invariant x1 <= x2; // 1) x1 <= x2 (from pre-condition), 2) x1 <= x2 && (x2' = x1 || x2' = x2) => x1 <= x2'
        {
            if (x2 < x1) {
                x2 := x1;
            }
            x4 := x4 + 1;
        }

        // post-condition
        assert(x1 >= x2);
    }
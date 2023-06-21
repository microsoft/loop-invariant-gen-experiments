procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;
        var nondet: bool;

        // pre-condition
        x4 := 1;
        x5 := 1;

        // loop body
        while (x4 < x6)
        invariant x4 >= 1; // 1) x4 = 1 => x4 >= 1, 2) x4 >= 1 && x' = x4 + 1 => x' >= 1
        invariant x4 <= x6; // 1) x4 = 1 => x4 <= x6, 2) x4 <= x6 && x' = x4 + 1 => x' <= x6
        invariant 1 <= x5 && x5 <= x4; // 1) x4 = 1, x5 = 1 => 1 <= x5 && x5 <= x4, 2) 1 <= x5 && x5 <= x4 && (x5' = x5 || x5' = x4) && x' = x4 + 1 => 1 <= x5' && x5' <= x'
        {
            havoc nondet;
            if (nondet) {
                x5 := x4;
            }
            x4 := x4 + 1;
        }

        // post-condition
        if (x6 > 1) {
            assert (x5 >= 1);
        }
    }
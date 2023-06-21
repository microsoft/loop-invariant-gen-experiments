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
        x4 := 0;
        x5 := 0;

        // loop body
        while (x4 < x6)
        invariant x4 >= 0; // 1) x4 = 0 => x4 >= 0, 2) x4 >=0 && x4' = x4 + 1 => x4' >= 0
        invariant x4 <= x6; // 1) x4 = 0 => x4 <= x6, 2) x4 <= x6 && x4' = x4 + 1 => x4' <= x6
        invariant 0 <= x5 && x5 <= x4; // 1) x4 = 0, x5 = 0 => 0 <= x5 && x5 <= x4, 2) 0 <= x5 && x5 <= x4 && (x5' = x5 || x5' = x4) && x4' = x4 + 1 => 0 <= x5' && x5' <= x4'
        invariant x6 == 0 || x4 <= x6;
        {
            havoc nondet;
            if (nondet) {
                x5 := x4;
            }
            x4 := x4 + 1;
        }

        // post-condition
        if (x6 > 0) {
            assert (x5 >= 0);
        }
    }
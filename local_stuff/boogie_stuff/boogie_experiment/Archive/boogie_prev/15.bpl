procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;
        x2 := 0;

        // loop body
        while (x1 < x3)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >=0 && x1' = x1 + 1 => x1' >= 0
        invariant x1 <= x3; // 1) x1 = 0 => x1 <= x3, 2) x1 <= x3 && x1' = x1 + 1 => x1' <= x3
        invariant 0 <= x2 && x2 <= x1; // 1) x1 = 0, x2 = 0 => 0 <= x2 && x2 <= x1, 2) 0 <= x2 && x2 <= x1 && (x2' = x2 || x2' = x1) && x1' = x1 + 1 => 0 <= x2' && x2' <= x1'
        {
            havoc nondet;
            if (nondet) {
                x2 := x1;
            }
            x1 := x1 + 1;
        }

        // post-condition
        if (x3 > 0) {
            assert (x2 < x3);
            //assert (x2 >= 0); // This assertion is already covered by the loop invariant "0 <= x2 && x2 <= x1"
        }
    }
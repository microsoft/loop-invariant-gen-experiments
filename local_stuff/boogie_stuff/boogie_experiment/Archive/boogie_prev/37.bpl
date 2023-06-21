procedure main()
    {
        var x1: int;
        var nondet: bool;
        var nondet2: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (nondet)
        invariant 0 <= x1 && x1 <= 40; // 1) x1 = 0 => 0 <= x1 && x1 <= 40, 2) 0 <= x1 && x1 <= 40 && (x1' = x1 + 1 || x1' = 1 || x1' = x1) => 0 <= x1' && x1' <= 40
        {
            havoc nondet2;
            if (nondet2) {
                if (x1 != 40) {
                    x1 := x1 + 1;
                }
            } else {
                if (x1 == 40) {
                    x1 := 1;
                }
            }
        }

        // post-condition
        if (x1 < 0 || x1 > 40) {
            assert (x1 == 40);
        }
    }
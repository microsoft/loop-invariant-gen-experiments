procedure main()
    {
        var x1: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (*)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && (x1' = x1 + 1 || x1' = 1 || x1' = x1) => x1' >= 0
        invariant x1 <= 4; // 1) x1 = 0 => x1 <= 4, 2) x1 <= 4 && (x1' = x1 + 1 || x1' = 1 || x1' = x1) => x1' <= 4
        {
            havoc nondet;
            if (nondet) {
                if (x1 != 4) {
                    x1 := x1 + 1;
                }
            } else {
                if (x1 == 4) {
                    x1 := 1;
                }
            }
        }

        // post-condition
        if (x1 != 4) {
            assert (x1 <= 4);
        }
    }
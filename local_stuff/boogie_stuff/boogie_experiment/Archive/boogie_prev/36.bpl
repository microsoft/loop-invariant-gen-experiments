procedure main()
    {
        var x1: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (*)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && (x1' = x1 + 1 || x1' = 1 || x1' = x1) => x1' >= 0
        invariant x1 <= 40; // 1) x1 = 0 => x1 <= 40, 2) x1 <= 40 && (x1' = x1 + 1 || x1' = 1 || x1' = x1) => x1' <= 40
        {
            havoc nondet;
            if (nondet) {
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
        if (x1 != 40) {
            assert (x1 <= 40);
        }
    }
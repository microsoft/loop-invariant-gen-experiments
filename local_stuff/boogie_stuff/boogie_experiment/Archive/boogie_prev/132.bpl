procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (nondet)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && x1' = x2 + x4 => x1' >= 0
        {
            havoc nondet;
            if (x3 > 48) {
                if (x3 < 57) {
                    x2 := x1 + x1;
                    x4 := x3 - 48;
                    x1 := x2 + x4;
                }
            }
        }

        // post-condition
        assert (x1 >= 0);
    }
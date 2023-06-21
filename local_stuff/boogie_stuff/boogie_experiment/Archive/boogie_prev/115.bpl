procedure main()
    {
        var x1: int;
        var x2: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;
        x2 := 0;

        // loop body
        while (nondet)
        invariant x1 == x2; // 1) x1 = 0, x2 = 0 => x1 == x2, 2) x1 == x2 && x1' = x1 + 1 && x2' = x2 + 1 => x1' == x2'
        {
            havoc nondet;
            x2 := x2 + 1;
            x1 := x1 + 1;
        }

        // post-condition
        if (x1 != -1) {
            assert (x1 == x2);
        }
    }
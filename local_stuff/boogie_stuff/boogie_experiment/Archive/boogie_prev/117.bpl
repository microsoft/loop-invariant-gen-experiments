procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var nondet: bool;

        // pre-condition
        x1 := 0;
        x5 := 0;

        // loop body
        while (nondet)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && x1' = x1 + 1 => x1' >= 0
        invariant x5 >= 0; // 1) x5 = 0 => x5 >= 0, 2) x5 >= 0 && x5' = x5 + 1 => x5' >= 0
        invariant x1 == x5; // 1) x1 = x5 = 0 => x1 == x5, 2) x1 == x5 && x1' = x1 + 1 && x5' = x5 + 1 => x1' == x5'
        {
            havoc nondet;
            x5 := x5 + 1;
            x1 := x1 + 1;
        }

        // post-condition
        if (x1 != -1) {
            assert (x1 == x5);
        }
    }
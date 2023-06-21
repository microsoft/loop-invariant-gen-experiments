procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var nondet: bool;

        // pre-conditions
        assume(x1 >= 0);
        assume(x1 <= 2);
        assume(x2 <= 2);
        assume(x2 >= 0);

        // loop body
        while (nondet)
        invariant x1 >= 0; // 1) x1 >= 0 => x1 >= 0, 2) x1 >= 0 && x1' = x1 + 2 => x1' >= 0
        invariant x1 <= 2 * x2; // 1) x1 <= 2 * x2 => x1 <= 2 * x2, 2) x1 <= 2 * x2 && x1' = x1 + 2 && x2' = x2 + 2 => x1' <= 2 * x2'
        {
            havoc nondet;
            x1 := x1 + 2;
            x2 := x2 + 2;
        }

        // post-condition
        if (x2 == 0) {
            assert(x1 != 4);
        }
    }
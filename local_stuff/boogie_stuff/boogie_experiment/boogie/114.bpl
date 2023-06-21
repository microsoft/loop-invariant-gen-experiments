procedure main()
    {
        var x1: int;
        var x2: int;
        var nondet: bool;

        // pre-conditions
        x1 := 0;
        x2 := 0;

        // loop body
        while (nondet)
        invariant x1 == x2;
        {
            havoc nondet;
            x2 := x2 + 1;
            x1 := x1 + 1;
        }

        // post-condition
        if (x1 != x2) {
            assert (x1 == -1);
        }
    }
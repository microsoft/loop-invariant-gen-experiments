procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var nondet: bool;

        // pre-conditions
        x3 := (x2 + 1);
        x1 := 0;

        // loop body
        while (x2 != x3)
        invariant x3 >= x2 + 1;
        invariant x1 == 0 || x1 == 1;
        invariant x1 == 1 || x2 != x3;
        {
            havoc nondet;
            if (nondet) {
                x1 := 1;
                x2 := x3;
            } else {
                x1 := 0;
                x2 := x3;
                x3 := (x3 + 1);
            }
        }

        // post-condition
        assert (x1 == 1);
    }
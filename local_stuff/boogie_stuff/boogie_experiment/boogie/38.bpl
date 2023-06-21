procedure main()
    {
        var x1: int;
        var x2: int;
        var nondet: bool;

        // pre-condition
        assume (x1 > 0);
        x2 := 0;

        // loop body
        while (nondet)
        invariant x2 >= 0;
        invariant x2 <= x1 + 1;
        {
            havoc nondet;
            if (x2 == x1) {
                x2 := 1;
            }
            else {
                x2 := x2 + 1;
            }
        }

        // post-condition
        if (x2 == x1) {
            assert (x2 >= 0);
        }
    }
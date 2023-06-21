procedure main()
    {
        var x1: int;
        var nondet1: bool;
        var nondet2: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (*)
        invariant x1 >= 0 && x1 <= 4;
        {
            havoc nondet1;
            havoc nondet2;
            if (nondet1) {
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
        if (x1 < 0 || x1 > 4) {
            assert(x1 == 4);
        }
    }
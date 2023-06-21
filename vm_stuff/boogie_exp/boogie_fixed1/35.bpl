procedure main()
    {
        var c: int;
        var nondet1: bool;
        var nondet2: bool;

        // pre-condition
        c := 0;

        // loop body
        while (*)
        invariant c >= 0;
        invariant c <= 40;
        {
            havoc nondet1;
            havoc nondet2;
            if (nondet1) {
                if (c != 40) {
                    c := c + 1;
                }
            } else {
                if (c == 40) {
                    c := 1;
                }
            }
        }

        // post-condition
        if (c != 40) {
            assert(c >= 0);
        }
    }
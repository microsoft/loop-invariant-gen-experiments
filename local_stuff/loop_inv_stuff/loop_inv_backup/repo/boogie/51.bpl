 procedure main()
    {
        var c: int;
        var nondet: bool;
        // pre-conditions
        c := 0;
        // loop body
        havoc nondet;
        while (nondet)
        invariant 0 <= c && c <= 4;
        {
            havoc nondet;
            if (nondet) {
                if (c != 4) {
                    c := c + 1;
                }
            } else {
                if (c == 4) {
                    c := 1;
                }
            }
        }
        // post-condition
        if (c != 4) {
            assert(c <= 4);
        }
    }
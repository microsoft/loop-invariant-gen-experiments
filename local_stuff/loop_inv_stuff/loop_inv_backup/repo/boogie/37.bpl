 procedure main()
    {
        var c: int;
        var nondet: bool;
        // pre-conditions
        c := 0;
        // loop body
        havoc nondet;
        while (nondet)
        invariant c >= 0 && c <= 40;
        {
            havoc nondet;
            if (nondet) {
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
        if (c < 0) {
            if (c > 40) {
                assert(c == 40);
            }
        }
    }
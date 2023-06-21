procedure main()
    {
        var z1: int;
        var z2: int;
        var z3: int;
        var x: int;
        var m: int;
        var n: int;
        var nondet: bool;

        // pre-condition
        x := 1;
        m := 1;

        // loop body
        while (x < n)
        invariant x >= 1;
        invariant 1 <= m && m <= x;
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }

        // post-condition
        if (n > 1) {
            assert (m >= 1);
        }
    }
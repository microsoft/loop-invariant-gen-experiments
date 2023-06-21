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
        x := 0;
        m := 0;

        // loop body
        while (x < n)
        invariant x >= 0;
        invariant 0 <= m && m <= x;
        invariant x == 0 || m < n;
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }

        // post-condition
        if (n > 0) {
            assert (m < n);
        }
    }
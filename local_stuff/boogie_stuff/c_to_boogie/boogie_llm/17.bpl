procedure main()
    {
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
        invariant x == 1 || m < n;
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }

        // post-condition
        if (n > 1) {
            assert (m < n);
        }
    }
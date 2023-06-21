 procedure main()
    {
        var x: int;
        var m: int;
        var n: int;
        var nondet: bool;

        x := 1;
        m := 1;

        while (x < n)
        invariant x >= 1 && m >= 1 && m <= x;
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }

        if (n > 1) {
            assert (m >= 1);
        }
    }
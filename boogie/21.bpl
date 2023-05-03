 procedure main()
    {
        var z1: int;
        var z2: int;
        var z3: int;
        var x: int;
        var m: int;
        var n: int;
        var nondet: bool;
        x := 1;
        m := 1;
        havoc nondet;
        while (x < n)
        invariant m <= x && x <= n;
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }
        if (n > 1) {
            assert(m < n);
            //assert(m >= 1);
        }
    }
 procedure main()
    {
        var z1: int;
        var z2: int;
        var z3: int;
        var x: int;
        var m: int;
        var n: int;
        var nondet: bool;
        x := 0;
        m := 0;
        havoc nondet;
        while (x < n)
            invariant x <= n;
            invariant (x > 0) ==> (m >= 0 && m < x);
        {
            havoc nondet;
            if (nondet) {
                m := x;
            }
            x := x + 1;
        }
        if (n > 0) {
            assert (m < n);
            //assert (m >= 0);
        }
    }
 procedure main()
    {
        var x: int;
        var m: int;
        var n: int;
        var nondet: bool;
        x := 0;
        m := 0;
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
        if(n > 0) {
            assert (m < n);
            //assert (m >= 0);
        }
    }
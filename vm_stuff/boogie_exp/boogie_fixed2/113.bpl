procedure main()
    {
        var i: int;
        var n: int;
        var sn: int;
        var v1: int;
        var v2: int;
        var v3: int;

        // pre-conditions
        sn := 0;
        i := 1;

        // loop body
        while (i <= n)
        invariant i >= 1;
        invariant sn == i - 1;
        invariant sn <= n;
        invariant i <= n + 1;
        {
            i := i + 1;
            sn := sn + 1;
        }

        // post-condition
        if (sn != 0) {
            assert(sn == n);
        }
    }
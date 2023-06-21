procedure main()
    {
        var i: int;
        var n: int;
        var sn: int;

        // pre-condition
        sn := 0;
        i := 1;
        
        // loop body
        while (i <= n)
        invariant i >= 1;
        invariant sn >= 0;
        invariant sn == (i * (i - 1)) / 2;
        {
            i := i + 1;
            sn := sn + i - 1;
        }

        // post-condition
        if (sn != 0) {
            assert (sn == (n * (n + 1)) / 2);
        }
    }
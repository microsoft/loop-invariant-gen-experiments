 procedure main()
    {
        var i: int;
        var sn: int;
        // pre-conditions
        sn := 0;
        i := 1;
        // loop body
        while (i <= 8)
        invariant i - 1 <= sn && sn <= i - 1;
        {
            i := i + 1;
            sn := sn + 1;
        }
        // post-condition
        if (sn != 0)
        {
            assert(sn == 8);
        }
    }
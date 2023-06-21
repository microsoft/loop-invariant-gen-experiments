 procedure main()
    {
        var i: int;
        var size: int;
        var sn: int;
        var v1: int;
        var v2: int;
        var v3: int;
        // pre-conditions
        sn := 0;
        i := 1;
        // loop body
        while (i <= size)
            invariant i - 1 == sn;
        {
            i := i + 1;
            sn := sn + 1;
        }
        // post-condition
        if (sn != 0)
        {
            assert(sn == size);
        }
    }
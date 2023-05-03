 procedure main()
    {
        var i: int;
        var x: int;
        var y: int;
        var nondet: bool;
        // pre-conditions
        i := 0;
        assume(x >= 0);
        assume(y >= 0);
        assume(x >= y);
        // loop body
        havoc nondet;
        while (nondet)
        invariant i >= 0 && i <= y;
        {
            havoc nondet;
            if (i < y)
            {
                i := i + 1;
            }
        }
        // post-condition
        if (i >= x)
        if (0 > i)
        assert(i >= y);
    }
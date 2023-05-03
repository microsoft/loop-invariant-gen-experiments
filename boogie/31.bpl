 procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;
        // pre-conditions
        x := n;
        // loop body
        while (x > 1)
        invariant x >= 1;
        {
            x := x - 1;
        }
        // post-condition
        if (x != 1)
        {
            assert(n < 0);
        }
    }
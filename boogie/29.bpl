 procedure main()
    {
        var n: int;
        var x: int;
        // pre-conditions
        x := n;
        // loop body
        while (x > 0)
        invariant x <= n && x >= 0;
        {
            x := x - 1;
        }
        // post-condition
        if (n >= 0) {
            assert(x == 0);
        }
    }
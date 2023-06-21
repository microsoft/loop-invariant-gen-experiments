procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;

        // pre-condition
        x := n;

        // loop body
        while (x > 0)
        invariant x >= 0;
        invariant x <= n;
        {
            x := x - 1;
        }

        // post-condition
        if (x != 0) {
            assert(n < 0);
        }
    }
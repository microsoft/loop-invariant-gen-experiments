 procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;
        // pre-conditions
        x := 0;
        // loop body
        while (x < n)
        invariant x <= n;
        {
            x := x + 1;
        }
        // post-condition
        if (n >= 0) {
            assert(x == n);
        }
    }
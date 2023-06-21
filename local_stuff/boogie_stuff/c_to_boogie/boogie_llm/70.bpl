procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;
        var y: int;

        // pre-condition
        x := 1;

        // loop body
        while (x <= n)
        invariant x >= 1;
        invariant (x == 1 || y < n);
        {
            y := n - x;
            x := x + 1;
        }

        // post-condition
        if (n > 0) {
            assert (y < n);
        }
    }
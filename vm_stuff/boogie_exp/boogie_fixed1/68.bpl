procedure main()
    {
        var n: int;
        var y: int;
        var x: int;

        // pre-condition
        x := 1;

        // loop body
        while (x <= n)
        invariant x >= 1;
        invariant 0 <= y && y <= n;
        invariant x == 1 || y == n - (x - 1);
        {
            y := n - x;
            x := x + 1;
        }

        // post-condition
        if (n > 0) {
            assert (y <= n);
        }
    }
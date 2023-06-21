procedure main()
    {
        var n: int;
        var x: int;
        var y: int;

        // pre-conditions
        assume(n >= 0);
        x := n;
        y := 0;

        // loop body
        while (x > 0)
        invariant x >= 0;
        invariant y == n - x;
        {
            y := y + 1;
            x := x - 1;
        }

        // post-condition
        assert (y == n);
    }
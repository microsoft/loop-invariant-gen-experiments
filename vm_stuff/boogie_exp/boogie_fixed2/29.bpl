procedure main()
    {
        var n: int;
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
        if (n >= 0) {
            assert (x == 0);
        }
    }
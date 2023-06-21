procedure main()
    {
        var x: int;
        var y: int;

        // pre-condition
        x := 1;
        y := 0;

        // loop body
        while (y < 100000)
        invariant y >= 0;
        invariant x >= y;
        {
            x := x + y;
            y := y + 1;
        }

        // post-condition
        assert (x >= y);
    }
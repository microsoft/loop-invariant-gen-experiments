procedure main()
    {
        var x: int;
        var y: int;

        // pre-condition
        x := 1;

        // loop body
        while (x <= 10)
        invariant x >= 1 && x <= 11;
        invariant 0 <= y && y <= 9;
        {
            y := 10 - x;
            x := x + 1;
        }

        // post-condition
        assert (y >= 0);
    }
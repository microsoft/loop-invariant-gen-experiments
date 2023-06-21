procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := -50;
        x2 := 0;

        // loop body
        while (x1 < 0)
        invariant x1 + x2 * (x2 - 1) div 2 >= -50;
        invariant x2 >= 0;
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x2 >= 0);
    }
procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-conditions
        x1 := 1;
        x2 := 0;

        // loop body
        while (x2 < 1000)
        invariant x2 >= 0;
        invariant x1 == x2 * (x2 + 1) div 2 + 1;
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x1 >= x2);
    }

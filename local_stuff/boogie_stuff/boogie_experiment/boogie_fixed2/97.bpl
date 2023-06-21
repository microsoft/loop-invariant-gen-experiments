procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;

        // pre-conditions
        x2 := 0;
        x1 := 0;
        x4 := 2;

        // loop body
        while (x1 <= x3)
        invariant x1 >= 0;
        invariant x2 == x1 * x4;
        {
            x1 := x1 + 1;
            x2 := x2 + x4;
        }

        // post-condition
        if (x4 == 1) {
            assert (x1 == x2);
        }
    }
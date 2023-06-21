procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-condition
        x3 := 1;

        // loop body
        while (x3 <= x1)
        invariant x3 >= 1;
        invariant x2 <= x1;
        {
            x2 := x1 - x3;
            x3 := x3 + 1;
        }

        // post-condition
        if (x1 > 0) {
            assert (x2 <= x1);
        }
    }
procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x2 := 0;

        // loop body
        while (x2 < x1)
        invariant x2 >= 0;
        {
            x2 := x2 + 1;
        }

        // post-condition
        if (x2 != x1) {
            assert (x1 < 0);
        }
    }
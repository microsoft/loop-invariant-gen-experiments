procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x2 := x1;

        // loop body
        while (x2 > 1)
        invariant x2 >= 1;
        invariant x2 <= x1;
        {
            x2 := x2 - 1;
        }

        // post-condition
        if (x2 != 1) {
            assert(x1 < 0);
        }
    }
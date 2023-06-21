procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;
        x2 := 10;

        // loop body
        while (x2 >= x1)
        invariant x1 >= 1;
        invariant x2 >= 6;
        invariant x1 + x2 <= 17;
        invariant x1 % 2 == 1;
        {
            x1 := x1 + 2;
            x2 := x2 - 1;
        }

        // post-condition
        assert (x2 == 6);
    }
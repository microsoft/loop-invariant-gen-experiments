procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;

        // loop body
        while (x1 <= 100)
        invariant x1 >= 1 && x1 <= 101;
        invariant x2 == 100 - x1 + 1;
        {
            x2 := 100 - x1;
            x1 := x1 + 1;
        }

        // post-condition
        assert (x2 >= 0);
    }
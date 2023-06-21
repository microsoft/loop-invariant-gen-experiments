procedure main()
    {
        var x1: int;

        // pre-condition
        x1 := 100;

        // loop body
        while (x1 > 0)
        invariant x1 >= 0; // 1) x1 = 100 => x1 >= 0, 2) x1 > 0 && x1' = x1 - 1 => x1' >= 0
        {
            x1 := x1 - 1;
        }

        // post-condition
        assert (x1 == 0);
    }
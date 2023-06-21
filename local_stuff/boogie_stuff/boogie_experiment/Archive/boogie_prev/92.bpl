procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-condition
        x1 := 0;
        x2 := 0;

        // loop body
        while (x2 >= 0)
        invariant x1 == 0; // 1) x1 = 0 => x1 == 0, 2) x1 == 0 && x2' = x2 + x1 => x1' == 0
        invariant x2 >= 0; // 1) x2 = 0 => x2 >= 0, 2) x2 >= 0 && x2' = x2 + x1 => x2' >= 0
        {
            x2 := x2 + x1;
        }

        // post-condition
        assert (x2 >= 0);
    }
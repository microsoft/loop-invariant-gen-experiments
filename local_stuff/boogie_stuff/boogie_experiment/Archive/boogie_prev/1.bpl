procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;
        x2 := 0;

        // loop body
        while (x2 < 100000)
        invariant x2 >= 0; // 1) x2 = 0 => x2 >= 0, 2) x2 >= 0 && x2' = x2 + 1 => x2' >= 0
        invariant x1 >= x2; // 1) x1 = 1, x2 = 0 => x1 >= x2, 2) x1 >= x2 && x1' = x1 + x2 && x2' = x2 + 1 => x1' >= x2'
        {
            x1 := x1 + x2;
            x2 := x2 + 1;
        }

        // post-condition
        assert (x1 >= x2);
    }
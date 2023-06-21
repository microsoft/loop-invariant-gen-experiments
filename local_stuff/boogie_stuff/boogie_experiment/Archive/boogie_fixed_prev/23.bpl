procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;
        x2 := 20;

        // loop body
        while (x2 >= x1)
        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 2 => x1' >= 1
        invariant x2 <= 20; // 1) x2 = 20 => x2 <= 20, 2) x2 <= 20 && x2' = x2 - 1 => x2' <= 20
        invariant x2 >= x1 - 1; // 1) x1 = 1, x2 = 20 => x2 >= x1 - 1, 2) x2 >= x1 - 1 && x1' = x1 + 2 && x2' = x2 - 1 => x2' >= x1' - 1
        {
            x1 := x1 + 2;
            x2 := x2 - 1;
        }

        // post-condition
        assert (x2 == 13);
    }
procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;
        x2 := 10;

        // loop body
        while (x2 >= x1)
        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 2 => x1' >= 1
        invariant x2 <= 10; // 1) x2 = 10 => x2 <= 10, 2) x2 <= 10 && x2' = x2 - 1 => x2' <= 10
        invariant x1 + x2 >= 11; // 1) x1 = 1, x2 = 10 => x1 + x2 >= 11, 2) x1 + x2 >= 11 && x1' = x1 + 2 && x2' = x2 - 1 => x1' + x2' >= 11
        {
            x1 := x1 + 2;
            x2 := x2 - 1;
        }

        // post-condition
        assert (x2 == 6);
    }
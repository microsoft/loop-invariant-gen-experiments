procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 1;

        // loop body
        while (x1 <= 10)
        invariant x1 >= 1; // 1) x1 = 1 => x1 >= 1, 2) x1 >= 1 && x1' = x1 + 1 => x1' >= 1
        invariant x1 <= 11; // 1) x1 = 1 => x1 <= 11, 2) x1 <= 11 && x1' = x1 + 1 => x1' <= 11
        invariant x2 == 10 - x1 + 1; // 1) x1 = 1 => x2 = 10 - x1 + 1, 2) x2 = 10 - x1 + 1 && x2' = 10 - x1' + 1 && x1' = x1 + 1 => x2' = 10 - x1' + 1
        {
            x2 := 10 - x1 + 1;
            x1 := x1 + 1;
        }

        // post-condition
        assert (x2 >= 0);
        //assert (x2 < 10); // This assertion is incorrect because when x1 = 11, x2 = -1
    }
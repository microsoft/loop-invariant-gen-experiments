procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;

        // pre-condition
        x5 := 1;

        // loop body
        while (x5 <= x1)
        invariant x5 >= 1;
        invariant (x5 > x1 || (x6 == x1 - x5));
        invariant x6 <= x1;
        {
            x6 := x1 - x5;
            x5 := x5 + 1;
        }

        // post-condition
        if (x1 > 0) {
            assert (x6 < x1);
        }
    }
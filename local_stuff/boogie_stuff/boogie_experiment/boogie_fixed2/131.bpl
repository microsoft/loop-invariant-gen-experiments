procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;

        // pre-condition
        x1 := 1;
        x2 := 1;
        x3 := 1;
        x4 := 1;

        // loop body
        while (x4 > 0)
        invariant x4 >= 0;
        invariant (x4 == 1 || x6 >= 0);
        {
            if (x5 > 0) {
                if (x6 > 0) {
                    x4 := x4 - x1;
                    x5 := x5 - x2;
                    x6 := x6 - x3;
                }
            }
        }

        // post-condition
        assert (x6 >= 0);
    }
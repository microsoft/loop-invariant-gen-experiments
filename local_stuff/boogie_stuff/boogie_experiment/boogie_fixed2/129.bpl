procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;

        // pre-condition
        x1 := 1;

        // loop body
        while (x1 < x2)
        invariant x1 >= 1;
        {
            x1 := x1 + x1;
        }

        // post-condition
        assert (x1 >= 1);
    }
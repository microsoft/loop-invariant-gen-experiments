procedure main()
    {
        var x: int;
        var y: int;
        var z1: int;
        var z2: int;
        var z3: int;

        // pre-condition
        x := 1;

        // loop body
        while (x < y)
        invariant x >= 1;
        invariant x <= y;
        {
            x := x + x;
        }

        // post-condition
        assert (x >= 1);
    }
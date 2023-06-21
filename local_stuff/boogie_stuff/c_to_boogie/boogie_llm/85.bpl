procedure main()
    {
        var x: int;
        var y: int;
        var z1: int;
        var z2: int;
        var z3: int;

        // pre-condition
        x := -15000;
        y := 0;
        
        // loop body
        while (x < 0)
        invariant x <= 0;
        invariant y >= 0;
        invariant x + y*y >= -15000;
        {
            x := x + y;
            y := y + 1;
        }

        // post-condition
        assert (y > 0);
    }
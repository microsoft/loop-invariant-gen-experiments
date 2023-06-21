procedure main()
    {
        var x: int;
        var y: int;

        // pre-condition
        x := -5000;
        y := 0;
        
        // loop body
        while (x < 0)
        invariant x <= 0;
        invariant y >= 0;
        invariant x + y * y >= -5000;
        {
            x := x + y;
            y := y + 1;
        }

        // post-condition
        assert (y > 0);
    }
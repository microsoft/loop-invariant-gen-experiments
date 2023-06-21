procedure main()
    {
        var x: int;
        var y: int;

        // pre-condition
        x := 1;
        
        // loop body
        while (x <= 100)
        invariant x >= 1 && x <= 101;
        invariant 0 <= y && y <= 100;
        {
            y := 100 - x;
            x := x + 1;
        }

        // post-condition
        assert (y < 100);
    }
procedure main()
    {
        var x1: int;
        var x2: int;

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
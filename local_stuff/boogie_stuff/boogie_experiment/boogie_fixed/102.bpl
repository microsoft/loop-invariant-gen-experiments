procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x2 := 0;
        
        // loop body
        while (x2 < x1)
        invariant x2 >= 0;
        invariant x1 >= 0;
        invariant x2 <= x1;
        {
            x2 := x2 + 1;
        }

        // post-condition
        if (x1 >= 0) {
            assert (x2 == x1);
        }
    }
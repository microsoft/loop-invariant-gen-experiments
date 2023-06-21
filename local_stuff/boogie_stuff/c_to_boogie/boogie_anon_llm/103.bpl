procedure main()
    {
        var x1: int;

        // pre-condition
        x1 := 0;
        
        // loop body
        while (x1 < 100)
        invariant x1 >= 0;
        invariant x1 <= 100;
        {
            x1 := x1 + 1;
        }

        // post-condition
        assert (x1 == 100);
    }
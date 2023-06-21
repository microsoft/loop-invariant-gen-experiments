procedure main()
    {
        var x: int;

        // pre-condition
        x := 0;
        
        // loop body
        while (x < 100)
        invariant x >= 0;
        invariant x <= 100;
        {
            x := x + 1;
        }

        // post-condition
        assert (x == 100);
    }
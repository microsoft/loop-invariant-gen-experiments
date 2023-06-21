procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-condition
        x1 := 0;
        
        // loop body
        while (x1 < 500)
        invariant x1 >= 0;
        invariant (x1 == 0 || x3 >= x2);
        {
            x1 := x1 + 1;
            if (x3 <= x2) {
                x2 := x3;
            }
        }

        // post-condition
        assert (x3 >= x2);
    }
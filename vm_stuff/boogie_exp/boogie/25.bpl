procedure main()
    {
        var x: int;

        // pre-condition
        x := 10000;

        // loop body
        while (x > 0)
        invariant x >= 0;
        {
            x := x - 1;
        }

        // post-condition
        assert (x == 0);
    }
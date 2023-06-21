procedure main()
    {
        var x: int;
        var y: int;

        // pre-condition
        x := 0;
        y := 0;

        // loop body
        while (y >= 0)
        invariant y >= 0;
        {
            y := y + x;
        }

        // post-condition
        assert (false); // The loop will never terminate, so the assertion will never be reached.
    }
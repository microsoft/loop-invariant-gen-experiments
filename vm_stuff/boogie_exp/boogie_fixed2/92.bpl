procedure main()
    {
        var z1: int;
        var z2: int;
        var z3: int;
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
        assert (false); // The loop invariant contradicts the post-condition, so the code is incorrect.
    }
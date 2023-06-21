procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;

        // pre-condition
        x1 := 0;
        x2 := 0;

        // loop body
        while (x2 >= 0)
        invariant x2 >= 0;
        {
            x2 := x2 + x1;
        }

        // post-condition
        assert (x2 >= 0);
    }

Note: The given code has an infinite loop when x1 is 0 or a non-negative value. The loop invariant x2 >= 0 is trivially true, but the post-condition assertion will never be reached.
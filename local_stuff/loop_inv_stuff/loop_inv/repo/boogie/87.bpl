 procedure main()
    {
        var lock: int;
        var x: int;
        var y: int;
        // pre-conditions
        x := y;
        lock := 1;
        // loop body
        while (x != y)
        invariant lock == 1;
        {
            if (*)
            {
                lock := 1;
                x := y;
            }
            else
            {
                lock := 0;
                x := y;
                y := y + 1;
            }
        }
        // post-condition
        assert(lock == 1);
    }
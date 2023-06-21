 procedure main()
    {
        var z1: int;
        var z2: int;
        var z3: int;
        var x: int;
        var y: int;
        x := 0;
        y := 0;
        while (y >= 0)
        invariant y >= 0;
        {
            y := y + x;
        }
        assert(y >= 0);
    }
 procedure main()
    {
        var x: int;
        var y: int;
        var nondet: bool;
        // pre-conditions
        x := 0;
        y := 0;
        // loop body
        havoc nondet;
        while (y >= 0)
        invariant y >= 0;
        {
            havoc nondet;
            y := y + x;
        }
        // post-condition
        assert(y >= 0);
    }
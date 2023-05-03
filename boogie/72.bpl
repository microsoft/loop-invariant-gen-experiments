 procedure main()
    {
        var c: int;
        var y: int;
        var z: int;
        var nondet: bool;
        // pre-conditions
        c := 0;
        assume(y >= 0);
        assume(y >= 127);
        z := 36 * y;
        // loop body
        havoc nondet;
        while (nondet)
        invariant z == c + 36 * y;
        {
            havoc nondet;
            if (c < 36)
            {
                z := z + 1;
                c := c + 1;
            }
        }
        // post-condition
        if (c < 36)
        {
            assert(z < 4608);
        }
    }
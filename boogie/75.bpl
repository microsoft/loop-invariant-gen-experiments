 procedure main()
    {
        var c: int;
        var x1: int;
        var x2: int;
        var x3: int;
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
        invariant c >= 0 && c <= 36 && z >= 36 * y && z <= 36 * y + 36;
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
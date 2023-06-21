procedure main()
    {
        var x: int;
        var y: int;
        var z1: int;
        var z2: int;
        var z3: int;
        var nondet: bool;

        // pre-conditions
        assume(x >= 0);
        assume(x <= 2);
        assume(y <= 2);
        assume(y >= 0);

        // loop body
        while (nondet)
        invariant x >= 0;
        invariant y >= 0;
        invariant x <= 2 * (y + 1);
        invariant y <= 2 * (x + 1);
        {
            havoc nondet;
            x := x + 2;
            y := y + 2;
        }

        // post-condition
        if (y == 0) {
            assert(x != 4);
        }
    }
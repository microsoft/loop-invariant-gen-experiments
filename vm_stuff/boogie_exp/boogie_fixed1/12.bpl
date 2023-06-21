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
        assume(x <= 10);
        assume(y <= 10);
        assume(y >= 0);

        // loop body
        while (nondet)
        invariant x >= 0;
        invariant x <= 10 * (y + 1);
        invariant y >= 0;
        invariant y <= 10 * (x + 1);
        {
            havoc nondet;
            x := x + 10;
            y := y + 10;
        }

        // post-condition
        if (y == 0) {
            assert(x != 20);
        }
    }
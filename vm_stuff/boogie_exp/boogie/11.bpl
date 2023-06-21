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
        invariant x <= 20;
        invariant y >= 0;
        invariant y <= 20;
        invariant (x == 20) ==> (y != 0);
        {
            havoc nondet;
            x := x + 10;
            y := y + 10;
        }

        // post-condition
        if (x == 20) {
            assert(y != 0);
        }
    }
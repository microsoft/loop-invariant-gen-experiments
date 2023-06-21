procedure main()
    {
        var x: int;
        var y: int;
        var nondet: bool;

        // pre-conditions
        assume(x >= 0);
        assume(x <= 10);
        assume(y <= 10);
        assume(y >= 0);

        // loop body
        while (nondet)
        invariant x >= 0;
        invariant (x <= 10) || (x >= 20 && x % 10 == 0);
        invariant y >= 0;
        invariant (y <= 10) || (y >= 20 && y % 10 == 0);
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
procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var nondet: bool;

        // pre-conditions
        assume(x1 >= 0);
        assume(x1 <= 10);
        assume(x2 <= 10);
        assume(x2 >= 0);

        // loop body
        while (nondet)
        invariant x1 >= 0;
        invariant x1 <= 20;
        invariant x2 >= 0;
        invariant x2 <= 20;
        invariant (x1 == x2) || (x1 - x2 == 10) || (x2 - x1 == 10);
        {
            havoc nondet;
            x1 := x1 + 10;
            x2 := x2 + 10;
        }

        // post-condition
        if (x1 == 20) {
            assert(x2 != 0);
        }
    }
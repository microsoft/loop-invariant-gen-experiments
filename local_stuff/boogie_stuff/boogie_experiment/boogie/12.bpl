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
        invariant x1 <= 10 + 10 * (x2 div 10);
        invariant x2 >= 0;
        invariant x2 <= 10 + 10 * (x1 div 10);
        {
            havoc nondet;
            {
                x1 := x1 + 10;
                x2 := x2 + 10;
            }
        }

        // post-condition
        if (x2 == 0) {
            assert(x1 != 20);
        }
    }
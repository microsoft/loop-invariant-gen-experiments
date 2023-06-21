procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;
        var nondet: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 >= 0);
        assume(x3 >= 0);
        assume(x2 >= x3);

        // loop body
        while (true)
        invariant x1 >= 0;
        invariant x1 <= x3;
        {
            havoc nondet;
            if (!nondet) {
                break;
            }
            if (x1 < x3) {
                x1 := x1 + 1;
            }
        }

        // post-condition
        if (x1 < x3) {
            assert(0 <= x1);
        }
    }
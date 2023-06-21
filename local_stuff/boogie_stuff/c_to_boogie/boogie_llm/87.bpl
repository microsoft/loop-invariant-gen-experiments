procedure main()
    {
        var lock: int;
        var x: int;
        var y: int;
        var nondet: bool;

        // pre-conditions
        x := y;
        lock := 1;

        // loop body
        while (x != y)
        invariant lock == 1 || lock == 0;
        invariant (lock == 1) ==> (x == y);
        {
            havoc nondet;
            if (nondet) {
                lock := 1;
                x := y;
            } else {
                lock := 0;
                x := y;
                y := y + 1;
            }
        }

        // post-condition
        assert (lock == 1);
    }
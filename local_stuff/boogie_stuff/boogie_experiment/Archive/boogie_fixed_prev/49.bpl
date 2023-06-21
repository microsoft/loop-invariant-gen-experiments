procedure main()
    {
        var x1: int;
        var x2: int;
        var nondet: bool;
        var nondet2: bool;

        // pre-conditions
        x1 := 0;
        assume(x2 > 0);

        // loop body
        while (nondet)
        invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && (x1' = x1 + 1 || x1' = 1) => x1' >= 0
        invariant x1 <= x2 + 1; // 1) x1 = 0 => x1 <= x2 + 1, 2) x1 <= x2 + 1 && (x1' = x1 + 1 || x1' = 1) => x1' <= x2 + 1
        invariant x1 != x2 || nondet2; // 1) x1 = 0 => x1 != x2, 2) (x1 != x2 || nondet2) && (x1' = x1 + 1 || x1' = 1) => x1' != x2 || nondet2'
        {
            havoc nondet2;
            if (nondet2) {
                if (x1 != x2) {
                    x1 := x1 + 1;
                }
            } else {
                if (x1 == x2) {
                    x1 := 1;
                }
            }
        }

        // post-condition
        if (x2 <= -1) {
            assert(x1 != x2);
        }
    }
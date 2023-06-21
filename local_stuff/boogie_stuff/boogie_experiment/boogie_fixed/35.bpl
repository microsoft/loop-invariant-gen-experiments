procedure main()
    {
        var x1: int;
        var nondet1: bool;
        var nondet2: bool;

        // pre-condition
        x1 := 0;

        // loop body
        while (true)
        invariant x1 >= 0;
        invariant x1 <= 41;
        invariant x1 != 40 || x1 == 40;
        {
            havoc nondet1;
            if (nondet1) {
                havoc nondet2;
                if (nondet2) {
                    if (x1 != 40) {
                        x1 := x1 + 1;
                    }
                } else {
                    if (x1 == 40) {
                        x1 := 1;
                    }
                }
            } else {
                break;
            }
        }

        // post-condition
        if (x1 != 40) {
            assert(x1 >= 0);
        }
    }
procedure main()
    {
        var c: int;
        var y: int;
        var z: int;
        var nondet: bool;

        // pre-conditions
        c := 0;
        assume(y >= 0);
        assume(y >= 127);
        z := 36 * y;

        // loop body
        while (true)
        invariant c >= 0;
        invariant c <= 36;
        invariant z >= 36 * y;
        invariant z <= 36 * y + c;
        invariant c == 36 || z < 4608;
        {
            havoc nondet;
            if (!nondet) {
                break;
            }
            if (c < 36) {
                z := z + 1;
                c := c + 1;
            }
        }

        // post-condition
        if (c < 36) {
            assert(z < 4608);
        }
    }
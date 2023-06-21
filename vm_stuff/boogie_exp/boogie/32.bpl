procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;

        // pre-condition
        x := n;

        // loop body
        while (x > 1)
        invariant x >= 1 || x == n;
        {
            x := x - 1;
        }

        // post-condition
        if (n >= 0) {
            assert (x == 1);
        }
    }
procedure main()
    {
        var i: int;
        var j: int;
        var x: int;
        var y: int;

        // pre-condition
        i := x;
        j := y;

        // loop body
        while (x != 0)
        invariant x >= 0;
        invariant y >= 0;
        invariant i - x == j - y;
        invariant x <= i;
        invariant y <= j;
        {
            x := x - 1;
            y := y - 1;
        }

        // post-condition
        if (y != 0) {
            assert (i != j);
        }
    }
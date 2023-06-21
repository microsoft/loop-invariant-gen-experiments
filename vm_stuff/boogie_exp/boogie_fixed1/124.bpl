procedure main()
    {
        var i: int;
        var j: int;
        var x: int;
        var y: int;

        // pre-conditions
        i := x;
        j := y;

        // loop body
        while (x != 0)
        invariant x >= 0;
        invariant y == j - (i - x);
        invariant i == x || y < j;
        {
            x := x - 1;
            y := y - 1;
        }

        // post-condition
        if (i == j) {
            assert (y == 0);
        }
    }
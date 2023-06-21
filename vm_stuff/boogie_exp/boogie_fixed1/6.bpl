procedure main()
    {
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;
        var size: int;
        var y: int;
        var z: int;

        // pre-condition
        x := 0;

        // loop body
        while (x < size)
        invariant x >= 0;
        invariant (x == 0 || z >= y);
        {
            x := x + 1;
            if (z <= y) {
                y := z;
            }
        }

        // post-condition
        if (size > 0) {
            assert (z >= y);
        }
    }
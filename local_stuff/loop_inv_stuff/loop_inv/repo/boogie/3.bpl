 procedure main()
    {
        var x: int;
        var y: int;
        var z: int;
        x := 0;
        // loop body
        while (x < 5)
        invariant x <= 5;
        {
            x := x + 1;
            if (z <= y) {
                y := z;
            }
        }
        // post-condition
        assert(z >= y);
    }
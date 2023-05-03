 procedure main()
    {
        var x: int;
        var y: int;
        var z: int;
        x := 0;
        while (x < 500)
            invariant z >= y;
        {
            x := x + 1;
            if (z <= y) {
                y := z;
            }
        }
        assert (z >= y);
    }
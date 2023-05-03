 procedure main()
    {
        var x: int;
        var y: int;
        x := 1;
        while (x <= 10)
        invariant x >= 1 && x <= 11;
        {
            y := 10 - x;
            x := x + 1;
        }
        assert (y >= 0);
        //assert (y < 10);
    }
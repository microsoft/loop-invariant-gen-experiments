 procedure main()
    {
        var n: int;
        var v1: int;
        var v2: int;
        var v3: int;
        var x: int;
        var y: int;
        x := 1;
        while (x <= n)
        invariant x >= 1 && x <= n + 1;
        {
            y := n - x;
            x := x + 1;
        }
        if (n > 0) {
            assert(y < n);
        }
    }
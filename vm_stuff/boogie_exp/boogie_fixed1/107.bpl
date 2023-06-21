procedure main()
    {
        var a: int;
        var m: int;
        var j: int;
        var k: int;

        // pre-condition
        j := 0;
        k := 0;

        // loop body
        while (k < 1)
        invariant k >= 0;
        invariant k <= 1;
        invariant (k == 0 || a <= m);
        {
            if (m < a) {
                m := a;
            }
            k := k + 1;
        }

        // post-condition
        assert (a <= m);
    }
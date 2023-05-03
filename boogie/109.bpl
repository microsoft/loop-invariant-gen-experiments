 procedure main()
    {
        var a: int;
        var c: int;
        var m: int;
        var j: int;
        var k: int;

        j := 0;
        k := 0;

        while (k < c)
            invariant k <= c && (k == 0 || m >= a);
        {
            if (m < a)
            {
                m := a;
            }
            k := k + 1;
        }

        if (c > 0)
        {
            assert(a <= m);
        }
    }
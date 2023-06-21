 procedure main()
    {
        var a: int;
        var m: int;
        var j: int;
        var k: int;

        j := 0;
        k := 0;

        while (k < 1)
            invariant m >= a || k == 0;
        {
            if (m < a)
            {
                m := a;
            }
            k := k + 1;
        }

        assert(a <= m);
    }
 procedure main()
    {
        var a: int;
        var m: int;
        var j: int;
        var k: int;
        // pre-conditions
        assume(a <= m);
        assume(j < 1);
        k := 0;
        // loop body
        while (k < 1)
            invariant a <= m;
        {
            if (m < a)
            {
                m := a;
            }
            k := k + 1;
        }
        // post-condition
        assert(a >= m);
    }
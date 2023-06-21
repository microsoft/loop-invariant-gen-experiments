procedure main()
    {
        var i: int;
        var j: int;
        var k: int;
        var n: int;

        // pre-conditions
        assume(k >= 0);
        assume(n >= 0);
        i := 0;
        j := 0;

        // loop body
        while (i <= n)
        invariant i >= 0;
        invariant j >= 0;
        invariant j == (i * (i - 1)) div 2;
        {
            i := i + 1;
            j := j + i;
        }

        // post-condition
        assert((i + (j + k)) > (2 * n));
    }
procedure main()
    {
        var i: int;
        var j: int;

        // pre-condition
        i := 1;
        j := 20;

        // loop body
        while (j >= i)
        invariant i >= 1;
        invariant j >= 0;
        invariant j + i <= 21;
        {
            i := i + 2;
            j := j - 1;
        }

        // post-condition
        assert (j == 13);
    }
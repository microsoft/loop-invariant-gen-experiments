procedure main()
    {
        var i: int;
        var j: int;

        // pre-condition
        i := 1;
        j := 10;

        // loop body
        while (j >= i)
        invariant i >= 1;
        invariant j <= 10;
        invariant (j - i) % 3 == 0;
        {
            i := i + 2;
            j := j - 1;
        }

        // post-condition
        assert (j == 6);
    }
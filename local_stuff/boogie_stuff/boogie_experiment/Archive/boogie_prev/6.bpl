procedure main()
    {
        var x1: int;
        var x2: int;
        var x3: int;
        var x4: int;
        var x5: int;
        var x6: int;
        var x7: int;

        // pre-condition
        x4 := 0;

        // loop body
        while (x4 < x5)
        invariant x4 >= 0; // 1) x4 = 0 => x4 >= 0, 2) x4 >=0 && x4' = x4 + 1 => x4' >= 0
        invariant x4 <= x5; // 1) x4 = 0 => x4 <= x5, 2) x4 <= x5 && x4' = x4 + 1 => x4' <= x5
        invariant (x4 == 0 || x7 >= x6); // 1) x4 = 0 => (x4==0 || x7>=x6), 2) x4 >=0 && (x4==0 || x7>=x6) && x4' = x4 + 1 && ((x7 <= x6 => x6' = x7) || (!(x7 <= x6) => x6' = x6)) && x7' = x7 =>  (x4'==0 || x7' >= x6')
        {
            x4 := x4 + 1;
            if (x7 <= x6) {
                x6 := x7;
            }
        }

        // post-condition
        if (x5 > 0) {
            assert (x7 >= x6);
        }
    }
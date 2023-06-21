procedure main()
    {
        var x1: int;
        var x2: int;

        // pre-condition
        x1 := 0;
        x2 := 0;

        // loop body
        while (x2 >= 0)
        invariant x2 >= 0; // 1) x2 = 0 => x2 >= 0, 2) x2 >= 0 && x2' = x2 + x1 => x2' >= 0 (since x1 = 0)
        {
            x2 := x2 + x1;
        }

        // post-condition
        // The loop invariant x2 >= 0 contradicts the loop condition x2 >= 0, so the loop will never terminate.
        // Therefore, the assertion x2 >= 0 after the loop is unreachable and cannot be proven.
    }
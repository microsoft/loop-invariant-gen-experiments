procedure main()
{
    var x1: int;
    var x2: int;
    var x3: int;
    var x4: int;
    var x5: int;
    var x6: int;
    var nondet: bool;

    // pre-conditions
    x1 := 0;
    assume(x4 >= 0);
    assume(x4 >= 127);
    x5 := (36 * x4);

    // loop body
    while (nondet)
    invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && x1' = x1 + 1 => x1' >= 0
    invariant x1 <= 36; // 1) x1 = 0 => x1 <= 36, 2) x1 <= 36 && x1' = x1 + 1 => x1' <= 36
    invariant x5 >= 36 * x4; // 1) x5 = 36 * x4 => x5 >= 36 * x4, 2) x5 >= 36 * x4 && x5' = x5 + 1 => x5' >= 36 * x4
    invariant x5 <= 36 * x4 + x1;
    {
        havoc nondet;
        if (x1 < 36)
        {
            x5 := (x5 + 1);
            x1 := (x1 + 1);
        }
    }

    // post-condition
    if (x1 < 36)
    {
        assert(x5 < 4608);
    }
}
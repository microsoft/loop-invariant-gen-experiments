procedure main()
{
    // variable declarations
    var x1: int;
    var x2: int;
    var x3: int;
    var x4: int;
    var x5: int;
    var x6: int;
    var x7: int;

    // pre-conditions
    assume (x1 == x3);
    assume (x2 == x4);

    // loop body
    while (x3 != 0)
    invariant x3 >= 0; // 1) x3 = x1 >= 0, 2) x3 >= 0 && x3' = x3 - 1 => x3' >= 0
    invariant x4 >= 0; // 1) x4 = x2 >= 0, 2) x4 >= 0 && x4' = x4 - 1 => x4' >= 0
    invariant x1 - x3 == x2 - x4; // 1) x1 - x3 = x2 - x4, 2) x1 - x3 = x2 - x4 && x3' = x3 - 1 && x4' = x4 - 1 => x1 - x3' = x2 - x4'
    {
        x3 := x3 - 1;
        x4 := x4 - 1;
    }

    // post-condition
    if (x1 == x2) {
        assert (x4 == 0);
    }
}
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
    x6 := x5 + 1;
    x1 := 0;

    // loop body
    while (x5 != x6)
    invariant x6 >= x5 + 1; // 1) x6 = x5 + 1 => x6 >= x5 + 1, 2) x6 >= x5 + 1 && x6' = x6 + 1 => x6' >= x5' + 1
    invariant x1 == 0 || x1 == 1; // 1) x1 = 0 => x1 == 0 || x1 == 1, 2) x1 == 0 || x1 == 1 && (x1' = 1 || x1' = 0) => x1' == 0 || x1' == 1
    invariant x5 != x6 || x1 == 1;
    {
        havoc nondet;
        if (nondet) {
            x1 := 1;
            x5 := x6;
        } else {
            x1 := 0;
            x5 := x6;
            x6 := x6 + 1;
        }
    }

    // post-condition
    assert (x1 == 1);
}
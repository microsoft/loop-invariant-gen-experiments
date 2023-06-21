procedure main()
{
    var x1: int;
    var x2: int;
    var x3: int;
    var x4: int;
    var nondet: bool;

    // pre-conditions
    assume(x2 >= 0);
    x1 := 0;
    x3 := 0;
    x4 := 0;

    // loop body
    while (x1 < x2)
    invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && x1' = x1 + 1 => x1' >= 0
    invariant x1 <= x2; // 1) x1 = 0 => x1 <= x2, 2) x1 <= x2 && x1' = x1 + 1 => x1' <= x2
    invariant 3 * x1 == x3 + x4; // 1) x1 = 0, x3 = 0, x4 = 0 => 3 * x1 == x3 + x4, 2) 3 * x1 == x3 + x4 && (x3' = x3 + 1 && x4' = x4 + 2 || x3' = x3 + 2 && x4' = x4 + 1) && x1' = x1 + 1 => 3 * x1' == x3' + x4'
    {
        x1 := x1 + 1;
        havoc nondet;
        if (nondet) {
            x3 := x3 + 1;
            x4 := x4 + 2;
        } else {
            x3 := x3 + 2;
            x4 := x4 + 1;
        }
    }

    // post-condition
    assert(3 * x2 == x3 + x4);
}
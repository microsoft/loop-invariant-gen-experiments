procedure main()
{
    var x1: int;
    var x2: int;
    var x3: int;
    var x4: int;
    var x5: int;
    var nondet: bool;

    // pre-conditions
    x1 := 0;
    assume(x2 > 0);

    // loop body
    while (unknown())
    invariant x1 >= 0; // 1) x1 = 0 => x1 >= 0, 2) x1 >= 0 && (x1' = x1 + 1 || x1' = 1) => x1' >= 0
    {
        havoc nondet;
        if (nondet) {
            if (x1 > x2) {
                x1 := x1 + 1;
            }
        } else {
            if (x1 == x2) {
                x1 := 1;
            }
        }
    }

    // post-condition
    if (x2 > -1) {
        assert(x1 != x2);
    }
}
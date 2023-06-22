procedure main()
{
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;

    // pre-conditions
    x := -50;
    assume(y >= 0); // Assuming y is non-negative

    // loop body
    while (x < 0)
    invariant x + y * (y - 1) div 2 = -50;
    invariant x < 0;
    invariant y >= 0;
    {
        x := x + y;
        y := y + 1;
    }

    // post-condition
    assert(y > 0);
}
procedure main()
{
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;

    // pre-conditions
    x := -50;
    y := 1; // Initializing y to 1 to satisfy the loop invariant

    // loop body
    while (x < 0)
    invariant x + y = -49;
    invariant x < 0;
    invariant y >= 1;
    {
        x := x + y;
        y := y + 1;
    }

    // post-condition
    assert(y > 0);
}
procedure main()
{
    var x: int;
    var y: int;

    // pre-conditions
    x := 1;
    y := 0;

    // loop body
    while (y < 100000)
    invariant x == 1 + y * (y - 1) div 2;
    {
        x := x + y;
        y := y + 1;
    }

    // post-condition
    assert(x >= y);
}
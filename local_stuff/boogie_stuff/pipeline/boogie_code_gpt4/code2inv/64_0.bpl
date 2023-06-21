procedure main()
{
    var x: int;
    var y: int;

    // pre-conditions
    x := 1;

    // loop body
    while (x <= 10)
    invariant x >= 1;
    invariant x <= 11;
    invariant y == 10 - (x - 1);
    {
        y := 10 - x;
        x := x + 1;
    }

    // post-conditions
    assert(y >= 0);
    assert(y < 10);
}
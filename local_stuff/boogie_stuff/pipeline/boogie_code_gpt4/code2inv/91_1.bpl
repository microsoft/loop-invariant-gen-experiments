procedure main()
{
    var x: int;
    var y: int;

    // pre-conditions
    x := 0;
    y := 0;

    // loop body
    while (y >= 0)
    invariant x == 0;
    invariant y >= 0;
    {
        y := y + x;
    }

    // post-condition
    assert(y >= 0);
}
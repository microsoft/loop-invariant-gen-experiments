procedure main()
{
    var x: int;
    var y: int;

    // pre-conditions
    x := 1;

    // loop body
    while (x <= 100)
    invariant x >= 1;
    invariant x <= 101;
    invariant y == (100 - x + 1);
    {
        y := 100 - x;
        x := x + 1;
    }

    // post-condition
    assert(y < 100);
}
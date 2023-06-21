procedure main()
{
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    x := 1;

    // loop body
    while (x <= 100)
    invariant x >= 1;
    invariant x <= 101;
    invariant y == 100 - x;
    {
        y := 100 - x;
        x := x + 1;
    }

    // post-conditions
    assert(y >= 0);
    assert(y < 100);
}
procedure main()
{
    var i: int;
    var j: int;
    var x: int;
    var y: int;

    // Initialization
    x := i;
    y := j;

    // loop body
    while (x != 0)
    invariant x >= 0;
    invariant y == j - (i - x);
    {
        x := x - 1;
        y := y - 1;
    }

    // post-condition
    if ((i == j) && (y != 0)) {
        assert(false);
    }
}
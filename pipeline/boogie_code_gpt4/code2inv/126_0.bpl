procedure main()
{
    var i: int;
    var j: int;
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;

    // pre-conditions
    i := x;
    j := y;

    // loop body
    while (x != 0)
    invariant i - x == z1;
    invariant j - y == z2;
    {
        x := x - 1;
        y := y - 1;
    }

    // post-condition
    if (i == j) {
        assert(y == 0);
    }
}
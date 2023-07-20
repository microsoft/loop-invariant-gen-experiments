procedure main()
{
    var i: int;
    var j: int;
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;

    // pre-conditions
    i := x;
    j := y;

    // loop body
    while (x != 0)
    invariant x >= 0;
    invariant (i - j) == (x - y);
    {
        x := x - 1;
        y := y - 1;
    }

    // post-condition
    if (y != 0) {
        assert(i != j);
    }
}
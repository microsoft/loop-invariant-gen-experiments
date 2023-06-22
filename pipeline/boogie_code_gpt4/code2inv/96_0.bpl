procedure main()
{
    var i: int;
    var j: int;
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    j := 0;
    i := 0;
    y := 1;

    // loop body
    while (i <= x)
    invariant i >= 0;
    invariant j == i * y;
    {
        i := i + 1;
        j := j + y;
    }

    // post-condition
    if (i != j) {
        assert(y != 1);
    }
}
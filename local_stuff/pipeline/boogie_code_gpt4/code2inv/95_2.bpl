procedure main()
{
    var i: int;
    var j: int;
    var x: int;
    var y: int;

    // pre-conditions
    assume(j == 0);
    assume(i == 0);
    assume(y == 1);
    assume(x >= 0); // assuming x is non-negative for proper loop behavior

    // loop body
    while (i <= x)
    invariant i >= 0;
    invariant j == i - 1;
    {
        i := i + 1;
        j := j + y;
    }

    // post-condition
    if (y == 1) {
        assert(i == j);
    }
}
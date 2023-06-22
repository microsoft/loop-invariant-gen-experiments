procedure main()
{
    var i: int;
    var x: int;
    var y: int;

    // pre-conditions
    i := 0;
    assume(x >= 0);
    assume(y >= 0);
    assume(x >= y);

    // loop body
    while (i < x)
    invariant i >= 0;
    invariant x >= 0;
    invariant y >= 0;
    invariant x >= y;
    invariant i <= y;
    {
        if (i < y) {
            i := i + 1;
        }
    }

    // post-condition
    if (i < y) {
        assert(i >= 0);
    }
}
procedure main()
{
    var i: int;
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    i := 0;
    assume(x >= 0);
    assume(y >= 0);
    assume(x >= y);

    // loop body
    while (nondet)
    invariant i <= y;
    invariant x >= 0;
    invariant y >= 0;
    invariant x >= y;
    {
        havoc nondet;
        if (i < y) {
            i := i + 1;
        }
    }

    // post-condition
    if (i < y) {
        assert(i < x);
    }
}
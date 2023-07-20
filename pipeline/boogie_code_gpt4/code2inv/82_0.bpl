procedure main()
{
    var i: int;
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;
    var nondet: bool;

    // pre-conditions
    i := 0;
    assume(x >= 0);
    assume(y >= 0);
    assume(x >= y);

    // loop body
    while (nondet)
    invariant i >= 0;
    invariant x >= 0;
    invariant y >= 0;
    invariant x >= y;
    invariant i <= y;
    {
        havoc nondet;
        if (i < y) {
            i := i + 1;
        }
    }

    // post-condition
    if (i >= x) {
        if (0 > i) {
            assert(i >= y);
        }
    }
}
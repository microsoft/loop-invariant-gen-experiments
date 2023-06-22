procedure main()
{
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 2);
    assume(y <= 2);
    assume(y >= 0);

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant x <= 2 + 2 * (y + 1);
    invariant y >= 0;
    invariant y <= 2 + 2 * (x + 1);
    {
        havoc nondet;
        x := x + 2;
        y := y + 2;
    }

    // post-condition
    if (x == 4) {
        assert(y != 0);
    }
}
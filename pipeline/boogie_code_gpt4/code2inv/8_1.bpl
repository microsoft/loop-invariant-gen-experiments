procedure main()
{
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 10);
    assume(y <= 10);
    assume(y >= 0);

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant y >= 0;
    invariant x - y >= -10;
    invariant x - y <= 10;
    {
        havoc nondet;
        x := x + 10;
        y := y + 10;
    }

    // post-condition
    if (y == 0) {
        assert(x != 20);
    }
}
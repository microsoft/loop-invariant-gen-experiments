procedure main()
{
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 2);
    assume(y >= 0);
    assume(y <= 2);

    // loop body
    while (nondet)
    invariant (0 <= x && x <= 2) || (2 <= x && x <= 4) || (4 <= x && x <= 6) || ...;
    invariant (0 <= y && y <= 2) || (2 <= y && y <= 4) || (4 <= y && y <= 6) || ...;
    {
        havoc nondet;
        x := x + 2;
        y := y + 2;
    }

    // post-condition
    if (y == 0) {
        assert(x < 4);
    }
}
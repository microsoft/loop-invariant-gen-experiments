procedure main()
{
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;
    var nondet: bool;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 2);
    assume(y <= 2);
    assume(y >= 0);

    // loop body
    while (nondet)
    invariant x % 2 == 0;
    invariant y % 2 == 0;
    invariant x >= 0;
    invariant x <= 4;
    invariant y >= 0;
    invariant y <= 4;
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
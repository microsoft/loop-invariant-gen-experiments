procedure main()
{
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;
    var nondet: bool;
    var constant: int;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 10);
    assume(y <= 10);
    assume(y >= 0);

    // set the constant for the loop invariant
    constant := x - y;

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant y >= 0;
    invariant x - y == constant;
    {
        havoc nondet;
        x := x + 10;
        y := y + 10;
    }

    // post-condition
    if (x == 20) {
        assert(y != 0);
    }
}
procedure main()
{
    var x: int;
    var y: int;
    var x_initial: int;
    var y_initial: int;
    var nondet: bool;

    // pre-conditions
    assume(x >= 0);
    assume(x <= 2);
    assume(y <= 2);
    assume(y >= 0);

    // Store the initial values of x and y
    x_initial := x;
    y_initial := y;

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant x <= 2 + 2 * (y + 1);
    invariant y >= 0;
    invariant y <= 2 + 2 * (x + 1);
    invariant x_initial + y_initial = x + y;
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
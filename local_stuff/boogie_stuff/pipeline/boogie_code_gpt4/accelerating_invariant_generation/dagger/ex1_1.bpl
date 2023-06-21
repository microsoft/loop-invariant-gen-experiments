procedure main()
{
    var x: int;
    var y: int;
    var xa: int := 0;
    var ya: int := 0;
    var nondet: bool;

    // loop body
    while (nondet)
    invariant x == xa + 2 * ya;
    invariant y == -2 * xa + ya;
    {
        havoc nondet;

        x := xa + 2 * ya;
        y := -2 * xa + ya;

        x := x + 1;

        if (nondet) {
            y := y + x;
        } else {
            y := y - x;
        }

        xa := x - 2 * y;
        ya := 2 * x + y;
    }

    // post-condition
    assert(xa + 2 * ya >= 0);
}
procedure main()
{
    var x: int;
    var y: int;
    var xa: int := 0;
    var ya: int := 0;
    var nondet: bool;

    // loop body
    while (nondet)
    invariant xa >= 0;
    invariant ya >= 0;
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
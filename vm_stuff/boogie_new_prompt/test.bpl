procedure main()
{
    // Variable declarations
    var x: int;
    var y: int;

    // Pre-conditions
    assume(x >= 0);
    assume(x <= 2);
    assume(y <= 2);
    assume(y >= 0);

    // Loop body
    while (*)
        invariant (x mod 2) == (y mod 2);
    {
        x := x + 2;
        y := y + 2;
    }

    // Post-condition
    if (y == 0) {
        assert(x != 4);
    }
}

procedure main()
{
    var x: int;
    var iterations: int;

    // pre-conditions
    assume(x == 100);
    assume(iterations == 0);

    // loop body
    while (x > 0)
    invariant x >= 0;
    invariant x <= 100;
    invariant x == 100 - iterations;
    {
        x := x - 1;
        iterations := iterations + 1;
    }

    // post-condition
    assert(x == 0);
}
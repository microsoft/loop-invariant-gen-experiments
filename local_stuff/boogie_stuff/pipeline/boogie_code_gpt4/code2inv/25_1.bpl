procedure main()
{
    var x: int;
    var remaining_iterations: int;

    // pre-conditions
    x := 10000;
    remaining_iterations := x;

    // loop body
    while (x > 0)
    invariant x >= 0;
    invariant x == remaining_iterations;
    {
        x := x - 1;
        remaining_iterations := remaining_iterations - 1;
    }

    // post-condition
    assert(x == 0);
}
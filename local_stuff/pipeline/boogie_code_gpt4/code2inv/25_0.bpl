procedure main()
{
    var x: int;
    var initial_x: int;
    var num_iterations: int;
    var nondet: bool;

    // pre-conditions
    initial_x := 10000;
    x := initial_x;
    num_iterations := 0;

    // loop body
    while (x > 0)
    invariant x >= 0;
    invariant initial_x - x == num_iterations;
    {
        x := x - 1;
        num_iterations := num_iterations + 1;
    }

    // post-condition
    assert(x == 0);
}
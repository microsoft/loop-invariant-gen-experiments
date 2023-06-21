procedure main()
{
    var n: int;
    var x: int;
    var executed_iterations: int;

    // pre-conditions
    x := n;
    executed_iterations := 0;

    // loop body
    while (x > 0)
    invariant x >= 0;
    invariant x + executed_iterations == n;
    {
        x := x - 1;
        executed_iterations := executed_iterations + 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == 0);
    }
}
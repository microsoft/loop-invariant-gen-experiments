procedure main()
{
    var n: int;
    var x: int;
    var num_iterations: int;

    // pre-conditions
    x := n;
    num_iterations := 0;

    // loop body
    while (x > 1)
    invariant x == n - num_iterations;
    {
        x := x - 1;
        num_iterations := num_iterations + 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == 1);
    }
}
procedure main()
{
    var n: int;
    var v1: int;
    var v2: int;
    var v3: int;
    var x: int;
    var iteration_count: int;

    // pre-conditions
    x := n;

    // loop body
    iteration_count := 0;
    while (x > 0)
    invariant x == n - iteration_count;
    invariant iteration_count >= 0;
    {
        x := x - 1;
        iteration_count := iteration_count + 1;
    }

    // post-condition
    if (x != 0) {
        assert(n < 0);
    }
}
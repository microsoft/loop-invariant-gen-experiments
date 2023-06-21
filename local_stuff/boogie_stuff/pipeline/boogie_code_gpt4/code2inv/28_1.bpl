procedure main()
{
    var n: int;
    var x: int;
    var iteration: int;
    var nondet: bool;

    // pre-conditions
    x := n;

    // loop body
    while (x > 0)
    invariant x == n - iteration;
    {
        x := x - 1;
        iteration := iteration + 1;
    }

    // post-condition
    if (x != 0) {
        assert(n < 0);
    }
}
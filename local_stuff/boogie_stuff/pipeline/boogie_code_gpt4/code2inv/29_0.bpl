procedure main()
{
    var n: int;
    var x: int;
    var nondet: bool;

    // pre-conditions
    x := n;

    // loop body
    while (x > 0)
    invariant x >= 0;
    invariant n - x >= 0;
    {
        x := x - 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == 0);
    }
}
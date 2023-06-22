procedure main()
{
    var n: int;
    var x: int;

    // pre-conditions
    x := n;

    // loop body
    while (x > 1)
    invariant x == n - (n - x);
    invariant x >= 1;
    {
        x := x - 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == 1);
    }
}
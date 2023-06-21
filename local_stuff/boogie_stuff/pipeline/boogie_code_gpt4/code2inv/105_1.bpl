procedure main()
{
    var n: int;
    var x: int;

    // pre-conditions
    x := 0;

    // loop body
    while (x < n)
    invariant x >= 0;
    invariant x <= n;
    {
        x := x + 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == n);
    }
}
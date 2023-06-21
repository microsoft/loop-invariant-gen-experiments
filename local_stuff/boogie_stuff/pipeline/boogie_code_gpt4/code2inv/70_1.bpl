procedure main()
{
    var n: int;
    var x: int;
    var y: int;
    var v1: int;
    var v2: int;
    var v3: int;

    // pre-conditions
    // n can have a garbage value, so no assumptions are made about it
    x := 1;

    // loop body
    while (x <= n)
    invariant x >= 1;
    invariant x <= n + 1;
    invariant x + y == n;
    {
        y := n - x;
        x := x + 1;
    }

    // post-condition
    if (n > 0) {
        assert(y < n);
    }
}
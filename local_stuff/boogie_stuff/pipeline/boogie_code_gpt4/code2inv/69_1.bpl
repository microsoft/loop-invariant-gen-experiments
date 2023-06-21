procedure main()
{
    var n: int;
    var x: int;
    var y: int;
    var v1: int;
    var v2: int;
    var v3: int;

    // pre-conditions
    // n can have any value (garbage value)
    x := 1;

    // loop body
    while (x <= n)
    invariant x >= 1;
    invariant y == n - x + 1;
    {
        y := n - x;
        x := x + 1;
    }

    // post-condition
    if (n > 0) {
        assert(y >= 0);
    }
}
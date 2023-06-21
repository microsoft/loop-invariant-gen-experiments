procedure main()
{
    var n: int;
    var x: int;
    var v1: int;
    var v2: int;
    var v3: int;

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
    if (x != n) {
        assert(n < 0);
    }
}
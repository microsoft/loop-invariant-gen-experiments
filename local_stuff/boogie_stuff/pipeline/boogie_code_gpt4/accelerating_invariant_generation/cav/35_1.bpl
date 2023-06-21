procedure main()
{
    var n: int;
    var x: int;

    // pre-conditions
    // n is uninitialized, so no pre-condition is needed for n
    x := 0;

    // loop body
    while (x <= n - 1)
    invariant x >= 0;
    invariant x <= n;
    {
        x := x + 1;
    }

    // post-condition
    if (x < n) {
        return;
    }
    assert(!(n >= 1 && (x <= n - 1 || x >= n + 1)));
}
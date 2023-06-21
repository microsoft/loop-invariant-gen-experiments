procedure main()
{
    var n: int;
    var x: int;

    // pre-conditions
    x := 0;
    assume(n >= 0);

    // loop body
    while (x < n)
    invariant x <= n;
    {
        x := x + 1;
    }

    // post-condition
    assert(x == n);
}
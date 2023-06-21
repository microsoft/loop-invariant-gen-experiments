procedure main()
{
    var n: int;
    var x: int;
    var k: int;

    // pre-conditions
    x := n;

    // loop body
    while (x > 0)
    invariant x == n - k;
    {
        x := x - 1;
        k := k + 1;
    }

    // post-condition
    if (x != 0) {
        assert(n < 0);
    }
}
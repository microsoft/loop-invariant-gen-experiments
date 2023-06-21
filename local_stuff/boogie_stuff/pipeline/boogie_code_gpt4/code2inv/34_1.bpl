procedure main()
{
    var n: int;
    var x: int;
    var i: int;

    // pre-conditions
    x := n;

    // loop body
    i := 0;
    while (x > 0)
    invariant x == n - i;
    {
        x := x - 1;
        i := i + 1;
    }

    // post-condition
    if (n >= 0) {
        assert(x == 0);
    }
}
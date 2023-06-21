procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 0;
    m := 0;

    // loop body
    while (x < n)
    invariant x >= 0;
    invariant x <= n;
    invariant m >= 0;
    invariant m <= x;
    {
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 0) {
        assert(m >= 0);
        assert(m < n);
    }
}
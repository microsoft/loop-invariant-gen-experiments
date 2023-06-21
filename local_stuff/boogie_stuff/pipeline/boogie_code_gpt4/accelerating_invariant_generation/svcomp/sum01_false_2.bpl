procedure main()
{
    var i: int;
    var n: int;
    var sn: int;

    // pre-conditions
    assume(n >= 0);

    sn := 0;
    i := 1;

    // loop body
    while (i <= n)
    invariant i >= 1;
    invariant sn == 2 * min(i - 1, 9);
    {
        if (i < 10) {
            sn := sn + 2;
        }
        i := i + 1;
    }

    // post-condition
    assert(sn == n * 2 || sn == 0);
}
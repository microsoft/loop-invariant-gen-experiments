procedure main()
{
    var i: int;
    var n: int;
    var sn: int;
    var nondet: bool;

    // pre-conditions
    sn := 0;
    i := 1;

    // loop body
    while (i <= n)
    invariant sn == i - 1;
    invariant 1 <= i <= n + 1;
    {
        i := i + 1;
        sn := sn + 1;
    }

    // post-condition
    if (sn != 0) {
        assert(sn == n);
    }
}
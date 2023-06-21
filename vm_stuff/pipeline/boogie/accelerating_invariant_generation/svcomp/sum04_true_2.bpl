procedure main()
{
    var i: int;
    var sn: int;

    // pre-conditions
    i := 1;
    sn := 0;

    // loop body
    while (i <= 8)
    invariant i >= 1;
    invariant i <= 9;
    invariant sn == 2 * (i - 1);
    {
        sn := sn + 2;
        i := i + 1;
    }

    // post-condition
    assert(sn == 8 * 2 || sn == 0);
}
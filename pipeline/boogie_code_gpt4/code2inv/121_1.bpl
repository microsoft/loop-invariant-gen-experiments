procedure main()
{
    var i: int;
    var sn: int;

    // pre-conditions
    assume(sn == 0);
    assume(i == 1);

    // loop body
    while (i <= 8)
    invariant sn == i - 1;
    invariant i <= 9;
    {
        i := i + 1;
        sn := sn + 1;
    }

    // post-condition
    if (sn != 0) {
        assert(sn == 8);
    }
}
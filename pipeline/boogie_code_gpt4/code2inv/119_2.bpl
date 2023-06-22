procedure main()
{
    var i: int;
    var size: int;
    var sn: int;

    // pre-conditions
    sn := 0;
    i := 1;

    // loop body
    while (i <= size)
    invariant i >= 1;
    invariant sn == i - 1;
    {
        i := i + 1;
        sn := sn + 1;
    }

    // post-condition
    if (sn != 0) {
        assert(sn == size);
    }
}
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
    invariant sn >= 0;
    invariant sn <= 6;
    {
        if (i < 4) {
            sn := sn + 2;
        }
        i := i + 1;
    }

    // post-condition
    assert(sn == 6);
}
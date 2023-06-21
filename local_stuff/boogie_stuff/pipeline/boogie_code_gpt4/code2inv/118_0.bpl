procedure main()
{
    var i: int;
    var size: int;
    var sn: int;
    var nondet: bool;

    // pre-conditions
    sn := 0;
    i := 1;

    // loop body
    while (i <= size)
    invariant sn == (i - 1);
    {
        i := i + 1;
        sn := sn + 1;
    }

    // post-condition
    if (sn != size) {
        assert(sn == 0);
    }
}
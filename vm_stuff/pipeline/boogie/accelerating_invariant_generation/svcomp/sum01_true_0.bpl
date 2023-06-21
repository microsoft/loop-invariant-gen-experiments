procedure main()
{
    var i: int;
    var n: int;
    var sn: int;
    var nondet: bool;

    // pre-conditions
    // n is assigned an unknown value, so we don't have any specific pre-conditions

    // initialization
    sn := 0;
    i := 1;

    // loop body
    while (i <= n)
    invariant i >= 1;
    invariant sn == 2 * (i - 1);
    {
        sn := sn + 2;
        i := i + 1;
    }

    // post-conditions
    assert(sn == n * 2 || sn == 0);
}
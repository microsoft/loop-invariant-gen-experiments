procedure main()
{
    var i: int;
    var n: int;
    var sn: int;
    var nondet: bool;

    // pre-conditions
    assume(n >= 0);

    // initialization
    sn := 0;
    i := 1;

    // loop body
    while (i <= n)
    invariant i >= 1;
    invariant sn == (i - 1) * 2 || (sn == -10 && i == 5);
    invariant i <= n + 1;
    {
        sn := sn + 2;
        if (i == 4) {
            sn := -10;
        }
        i := i + 1;
    }

    // post-condition
    assert(sn == n * 2 || sn == 0);
}
procedure main()
{
    var i: int;
    var j: int;
    var n: int;
    var sn: int;
    var nondet: bool;

    // pre-conditions
    assume(n >= 0);
    i := 1;
    j := 10;
    sn := 0;

    // loop body
    while (i <= n)
    invariant i >= 1;
    invariant j >= 0;
    invariant n >= 0;
    invariant sn >= 0;
    invariant sn == 2 * (i - 1) || sn == 0;
    {
        if (i < j) {
            sn := sn + 2;
        }
        j := j - 1;
        i := i + 1;
    }

    // post-condition
    assert(sn == n * 2 || sn == 0);
}
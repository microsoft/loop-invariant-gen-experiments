procedure main()
{
    var sn: int;
    var x: int;
    var nondet: bool;

    // pre-conditions
    assume(sn == 0);
    assume(x == 0);

    // loop body
    while (nondet)
    invariant sn == x;
    {
        havoc nondet;
        x := x + 1;
        sn := sn + 1;
    }

    // post-condition
    if (sn != -1) {
        assert(sn == x);
    }
}
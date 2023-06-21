procedure main()
{
    var sn: int;
    var loop1: int;
    var n1: int;
    var x: int;
    var nondet: bool;

    // pre-conditions
    assume(loop1 >= 0);
    assume(n1 >= 0);

    sn := 0;
    x := 0;

    // loop body
    while (true)
    invariant sn == x * 2 || sn == 0;
    invariant x >= 0;
    {
        if (x < 10) {
            sn := sn + 2;
        }
        x := x + 1;

        // post-condition
        assert(sn == x * 2 || sn == 0);
    }
}
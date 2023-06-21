procedure main()
{
    var cp1_off: int;
    var n1: int;
    var n2: int;
    var mc_i: int;
    var MAXDATA: int;
    var nondet: bool;

    // pre-conditions
    assume(MAXDATA > 0);
    assume(n1 <= MAXDATA * 2);
    assume(cp1_off <= n1);
    assume(n2 <= MAXDATA * 2 - n1);

    // loop body
    mc_i := 0;
    while (nondet)
    invariant mc_i >= 0;
    invariant mc_i <= n2;
    invariant cp1_off <= n1;
    invariant n1 <= MAXDATA * 2;
    invariant n2 <= MAXDATA * 2 - n1;
    invariant MAXDATA > 0;
    {
        havoc nondet;
        assert(cp1_off + mc_i < MAXDATA * 2);
        mc_i := mc_i + 1;
    }

    // post-condition
    assert(forall i: int :: (0 <= i && i < n2) ==> (cp1_off + i < MAXDATA * 2));
}
procedure main()
{
    var i: int;
    var x: int;
    var y: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    n := unknown_int();
    assume(n > 0);

    i := 0;
    x := 0;
    y := 0;

    // loop body
    while (i < n)
    invariant i >= 0;
    invariant i <= n;
    invariant x == y;
    {
        x := x - y;
        assert(x == 0);

        y := unknown_int();
        assume(y != 0);

        x := x + y;
        assert(x != 0);

        i := i + 1;
    }

    // post-condition
    assert(x == 0);
}
procedure main()
{
    var n: int;
    var x: int;
    var i: int;
    var nondet: bool;

    // pre-conditions
    x := n;

    // loop body
    i := 0;
    while (x > 1)
    invariant x == n - i;
    invariant i >= 0;
    {
        x := x - 1;
        i := i + 1;
    }

    // post-condition
    if (x != 1) {
        assert(n < 0);
    }
}
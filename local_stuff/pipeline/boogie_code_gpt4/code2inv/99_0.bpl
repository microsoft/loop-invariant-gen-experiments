procedure main()
{
    var n: int;
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    assume(n >= 0);
    x := n;
    y := 0;

    // loop body
    while (x > 0)
    invariant n == x + y;
    invariant x >= 0;
    invariant y >= 0;
    {
        y := y + 1;
        x := x - 1;
    }

    // post-condition
    assert(n == (x + y));
}
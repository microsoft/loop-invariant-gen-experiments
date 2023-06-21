procedure main()
{
    var n: int;
    var x: int;
    var y: int;

    // pre-conditions
    assume(n >= 0);

    x := n;
    y := 0;

    // loop body
    while (x > 0)
    invariant x + y == n;
    invariant x >= 0;
    invariant y >= 0;
    {
        x := x - 1;
        y := y + 1;
    }

    // post-condition
    assert(y == n);
}
procedure main()
{
    var x: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    assume(n > 0);

    // initialization
    x := 0;

    // loop body
    while (x < n)
    invariant x <= n;
    invariant n > 0;
    {
        x := x + 1;
    }

    // post-condition
    assert(x <= n);
}
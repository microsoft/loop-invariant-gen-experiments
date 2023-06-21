procedure main()
{
    var n: int;
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    // No specific pre-conditions are given for n and y, so we don't need to add any assume statements for them.

    // initialization
    x := 1;

    // loop body
    while (x <= n)
    invariant 1 <= x <= n+1;
    invariant y == n - (x - 1);
    {
        y := n - x;
        x := x + 1;
    }

    // post-conditions
    if (n > 0) {
        assert(y >= 0);
        //assert(y <= n); // This assertion is commented out in the original C code, but it's true and can be included.
    }
}
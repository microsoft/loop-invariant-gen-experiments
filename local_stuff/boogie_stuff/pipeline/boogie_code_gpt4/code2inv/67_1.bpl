procedure main()
{
    var n: int;
    var x: int;
    var y: int;
    var nondet: bool;

    // initialization
    x := 1;
    y := n;

    // loop body
    while (x <= n)
    invariant y + x == n + 1;
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
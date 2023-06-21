procedure main()
{
    var n: int;
    var x: int;
    var y: int;

    // initialization
    x := 1;

    // loop body
    while (x <= n)
    invariant y == n - x;
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
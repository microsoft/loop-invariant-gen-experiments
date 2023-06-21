procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 1;
    m := 1;
    // n is uninitialized, so we don't set a value for it

    // loop body
    while (x < n)
    invariant 1 <= m;
    invariant m <= x;
    invariant m == 1 || (m == x && unknown); // loop invariant
    {
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 1) {
        assert(m >= 1);
        // assert(m < n); // This assertion is commented out in the original C code
    }
}
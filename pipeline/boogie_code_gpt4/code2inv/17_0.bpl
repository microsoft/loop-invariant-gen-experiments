procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 1;
    m := 1;
    // n is uninitialized, so no pre-condition for it

    // loop body
    while (x < n)
    invariant x >= 1;
    invariant m >= 1;
    invariant m <= x;
    {
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 1) {
        assert(m < n);
        // assert(m >= 1); // This assertion is commented out in the original C code
    }
}
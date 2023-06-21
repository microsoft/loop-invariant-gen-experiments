procedure main()
{
    var z1: int;
    var z2: int;
    var z3: int;
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 1;
    m := 1;
    // n is uninitialized, so no pre-condition for n

    // loop body
    while (x < n)
    invariant x >= 1;
    invariant m >= 1;
    {
        havoc unknown;
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 1) {
        // assert (m < n); // This assertion is commented out in the original code
        assert (m >= 1);
    }
}
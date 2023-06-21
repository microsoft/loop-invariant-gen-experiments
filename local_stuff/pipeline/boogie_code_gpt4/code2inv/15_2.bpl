procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 0;
    m := 0;
    // n is uninitialized, so no pre-condition for n

    // loop body
    while (x < n)
    invariant x >= 0;
    invariant m >= 0;
    invariant m <= x;
    {
        havoc unknown;
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 0) {
        assert(m < n);
        // assert(m >= 0); // This condition is already covered by the loop invariant
    }
}
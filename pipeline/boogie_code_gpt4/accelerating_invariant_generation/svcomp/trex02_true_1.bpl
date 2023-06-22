procedure main()
{
    var x: int;
    var c: bool;

    // pre-conditions
    // x is initialized with an integer value from unknown_int()
    // c is initialized with a boolean value from unknown()

    // loop body
    while (x > 0)
    invariant x >= 0; // x is always non-negative
    {
        havoc c; // non-deterministically assign a boolean value to c
        if (c) {
            x := x - 1;
        } else {
            x := x - 1;
        }
    }

    // post-condition
    assert(x <= 0); // x is less than or equal to 0 after the loop
}
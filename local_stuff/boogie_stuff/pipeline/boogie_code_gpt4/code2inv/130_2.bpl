procedure main()
{
    var d1: int;
    var d2: int;
    var d3: int;
    var x1: int;
    var x2: int;
    var x3: int;
    var initial_x1: int;

    // Variable initializations
    d1 := 1;
    d2 := 1;
    d3 := 1;
    x1 := 1;
    initial_x1 := x1;

    // Pre-conditions
    assume(x2 >= 0);
    assume(x3 >= 0);

    // Loop body
    while (x1 > 0)
    invariant x1 >= 0;
    invariant x1 <= initial_x1;
    {
        if (x2 > 0) {
            if (x3 > 0) {
                x1 := x1 - d1;
                x2 := x2 - d2;
                x3 := x3 - d3;
            }
        }
    }

    // Post-conditions
    assert(x2 >= 0);
    // assert(x3 >= 0); // This assertion is commented out in the original C code
}
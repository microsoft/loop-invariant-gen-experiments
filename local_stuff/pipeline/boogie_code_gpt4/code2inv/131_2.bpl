procedure main()
{
    var d1: int;
    var d2: int;
    var d3: int;
    var x1: int;
    var x2: int;
    var x3: int;

    // pre-conditions
    d1 := 1;
    d2 := 1;
    d3 := 1;
    x1 := 1;
    assume(x2 >= 0); // assuming x2 is non-negative for simplicity
    assume(x3 >= 0); // assuming x3 is non-negative for simplicity

    // loop body
    while (x1 > 0)
    invariant x1 >= 0;
    {
        if (x2 > 0) {
            if (x3 > 0) {
                x1 := x1 - d1;
                x2 := x2 - d2;
                x3 := x3 - d3;
            }
        }
    }

    // post-condition
    assert(x1 >= 0);
}
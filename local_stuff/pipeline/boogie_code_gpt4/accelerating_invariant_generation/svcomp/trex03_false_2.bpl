procedure main()
{
    var x1: int;
    var x2: int;
    var x3: int;
    var d1: int;
    var d2: int;
    var d3: int;
    var c1: bool;
    var c2: bool;
    var nondet: bool;

    // pre-conditions
    assume(x1 >= 0);
    assume(x2 >= 0);
    assume(x3 >= 0);
    d1 := 1;
    d2 := 1;
    d3 := 1;

    // loop body
    while (x1 > 0 && x2 > 0 && x3 > 0)
    invariant x1 >= 0;
    invariant x2 >= 0;
    invariant x3 >= 0;
    {
        havoc c1;
        havoc c2;
        if (c1) {
            x1 := x1 - d1;
        } else if (c2) {
            x2 := x2 - d2;
        } else {
            x3 := x3 - d3;
        }
    }

    // post-condition
    assert(x1 == 0 && x2 == 0 && x3 == 0);
}
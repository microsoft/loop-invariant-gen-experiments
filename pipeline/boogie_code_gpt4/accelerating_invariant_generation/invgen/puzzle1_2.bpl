procedure main()
{
    var x1: int;
    var x2: int;
    var x3: int;
    var x4: int;
    var x5: int;
    var sum: int;
    var nondet: bool;

    // pre-conditions
    assume(x1 + x2 + x3 + x4 + x5 > 0);
    sum := x1 + x2 + x3 + x4 + x5;

    // loop body
    while (nondet)
    invariant x1 >= 0;
    invariant x2 >= 0;
    invariant x3 >= 0;
    invariant x4 >= 0;
    invariant x5 >= 0;
    invariant x1 + x2 + x3 + x4 + x5 == sum;
    invariant (x1 < 0) || (x2 < 0) || (x3 < 0) || (x4 < 0) || (x5 < 0);
    {
        havoc nondet;
        if (x1 < 0) {
            x1 := -x1;
            x5 := x5 - x1;
            x2 := x2 - x1;
        }
        else if (x2 < 0) {
            x2 := -x2;
            x1 := x1 - x2;
            x3 := x3 - x2;
        }
        else if (x3 < 0) {
            x3 := -x3;
            x2 := x2 - x3;
            x4 := x4 - x3;
        }
        else if (x4 < 0) {
            x4 := -x4;
            x3 := x3 - x4;
            x5 := x5 - x4;
        }
        else if (x5 < 0) {
            x5 := -x5;
            x4 := x4 - x5;
            x1 := x1 - x5;
        }
        else {
            assume false; // break the loop
        }
    }

    // post-conditions
    assert(x1 >= 0);
    assert(x2 >= 0);
    assert(x3 >= 0);
    assert(x4 >= 0);
    assert(x5 >= 0);
    assert(x1 + x2 + x3 + x4 + x5 == sum);
}
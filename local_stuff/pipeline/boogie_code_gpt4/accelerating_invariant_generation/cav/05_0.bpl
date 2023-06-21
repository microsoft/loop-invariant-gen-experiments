procedure main()
{
    var flag: bool;
    var x: int;
    var y: int;
    var i: int;
    var j: int;
    var nondet: bool;

    // pre-conditions
    assume(x == 0);
    assume(y == 0);
    assume(i == 0);
    assume(j == 0);

    // loop body
    while (nondet)
    invariant x == y;
    invariant i == x * (x + 1) div 2;
    invariant j == x * (x + 1) div 2 + (flag ? x : 0);
    {
        havoc nondet;
        x := x + 1;
        y := y + 1;
        i := i + x;
        j := j + y;
        if (flag) {
            j := j + 1;
        }
    }

    // post-condition
    assert(j >= i);
}
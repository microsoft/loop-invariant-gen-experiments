procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var nondet: bool;

    // pre-conditions
    x := 0;
    y := 0;

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant y >= 0;
    invariant x == 10 * y;
    {
        havoc nondet;
        x := x + 10;
        y := y + 1;
    }

    // post-condition
    assert(!(x <= z && y >= z + 1));
}
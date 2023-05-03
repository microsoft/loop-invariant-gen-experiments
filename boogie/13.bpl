 procedure main()
    {
    var x: int;
    var y: int;
    var z1: int;
    var z2: int;
    var z3: int;
    var nondet: bool;
    // pre-conditions
    assume(0 <= x);
    assume(x <= 2);
    assume(y <= 2);
    assume(y >= 0);
    // loop body
    havoc nondet;
    while (nondet)
    invariant x-y <= 2 && y - x <= 2;
    {
    havoc nondet;
    x := x + 2;
    y := y + 2;
    }
    // post-condition
    if(x==4) {
    assert(y != 0);
    }
    }
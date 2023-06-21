 procedure main()
    {
    var n: int;
    var v1: int;
    var v2: int;
    var v3: int;
    var x: int;
    // pre-conditions
    x := n;
    // loop body
    while (x > 0)
    invariant x >= 0;
    {
    x := x - 1;
    }
    // post-condition
    if(n >= 0) {
    assert(x == 0);
    }
    }
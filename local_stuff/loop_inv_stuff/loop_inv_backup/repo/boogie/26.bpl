 procedure main()
    {
    var n: int;
    var x: int;
    // pre-conditions
    x := n;
    // loop body
    while (x > 1)
    invariant x <= n;
    {
    x := x - 1;
    }
    // post-condition
    if(x != 1) {
    assert(n < 0);
    }
    }
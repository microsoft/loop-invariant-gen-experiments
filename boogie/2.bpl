 procedure main()
    {
    var x: int;
    var y: int;
    // pre-conditions
    x := 1;
    y := 0;
    // loop body
    while (y < 1000)
    invariant x >= y;
    {
    x := x + y;
    y := y + 1;
    }
    // post-condition
    assert(x >= y);
    }
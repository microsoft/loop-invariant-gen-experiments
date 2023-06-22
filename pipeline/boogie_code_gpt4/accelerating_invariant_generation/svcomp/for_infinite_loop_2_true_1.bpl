procedure main()
{
    var i: int;
    var x: int;
    var y: int;
    var n: int;

    // pre-conditions
    assume(n > 0);

    i := 0;
    x := 0;
    y := 0;

    // loop body
    while (true)
    invariant x == 0;
    invariant y == 0;
    invariant n > 0;
    {
        assert(x == 0);
        i := i + 1;
    }

    // post-condition (unreachable in this case)
    assert(x != 0);
}
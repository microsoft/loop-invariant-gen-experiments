procedure main()
{
    var x: int;
    var y: int;
    var C: int;

    // pre-conditions
    x := -5000;
    assume(y >= 0); // assuming y has a non-negative garbage value

    // loop invariants
    invariant x + y * (y - 1) div 2 == -5000 + C;

    // loop body
    while (x < 0)
    {
        x := x + y;
        y := y + 1;
    }

    // post-condition
    assert(y > 0);
}
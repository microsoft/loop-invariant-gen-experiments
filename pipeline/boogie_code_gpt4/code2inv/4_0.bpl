procedure main()
{
    var x: int;
    var y: int;
    var z: int;

    // pre-conditions
    assume(x == 0);

    // loop body
    while (x < 500)
    invariant x >= 0;
    invariant x <= 500;
    invariant (y <= z) || (y == min(y, z));
    {
        x := x + 1;
        if (z <= y) {
            y := z;
        }
    }

    // post-condition
    assert(z >= y);
}
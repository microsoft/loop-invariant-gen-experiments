procedure main()
{
    var x: int;
    var y: int;
    var z: int;

    // pre-conditions
    assume(x == 0);
    // No pre-conditions for y and z as they are uninitialized

    // loop body
    while (x < 5)
    invariant x >= 0;
    invariant x <= 5;
    {
        x := x + 1;
        if (z <= y) {
            y := z;
        }
    }

    // post-condition
    assert(z >= y);
}
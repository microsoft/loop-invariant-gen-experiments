procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var size: int;

    // pre-conditions
    // No explicit pre-conditions, but we can assume size, y, and z can have any integer values

    // loop body
    while (x < size)
    invariant x >= 0;
    invariant y <= z;
    {
        x := x + 1;
        if (z <= y) {
            y := z;
        }
    }

    // post-condition
    if (size > 0) {
        assert(z >= y);
    }
}
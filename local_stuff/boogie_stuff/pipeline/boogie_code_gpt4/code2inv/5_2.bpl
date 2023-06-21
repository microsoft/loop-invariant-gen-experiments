procedure main()
{
    var x: int;
    var size: int;
    var y: int;
    var z: int;

    // pre-conditions
    // Assuming size, y, and z are initialized with proper values
    assume(size >= 0);
    assume(y >= 0);
    assume(z >= 0);

    x := 0;

    // loop body
    while (x < size)
    invariant x >= 0;
    invariant x <= size;
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
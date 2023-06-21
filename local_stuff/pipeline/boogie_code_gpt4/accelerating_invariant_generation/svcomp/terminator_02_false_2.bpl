procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var tmp: bool;

    // pre-conditions
    // No specific pre-conditions for x, y, and z as they are initialized with unknown_int()

    // loop body
    while (x < 100 && 100 < z)
    invariant (x < 100 && 100 < z) || (x >= 100) || (z <= 100);
    {
        havoc tmp;
        if (tmp) {
            x := x + 1;
        } else {
            x := x - 1;
            z := z - 1;
        }
    }

    // post-condition
    assert(x >= 100 || z <= 100);
}
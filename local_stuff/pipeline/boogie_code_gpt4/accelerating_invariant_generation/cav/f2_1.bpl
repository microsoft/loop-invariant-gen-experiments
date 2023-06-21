procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var w: int;
    var unknown1: bool;
    var unknown2: bool;
    var unknown3: bool;

    // pre-conditions
    x := 0;
    y := 0;
    z := 0;
    w := 0;

    // loop body
    while (unknown1)
    invariant x >= 0;
    invariant y >= 0;
    invariant z >= 0;
    invariant w >= 0;
    invariant y >= 2 * x;
    {
        havoc unknown1;
        havoc unknown2;
        havoc unknown3;

        if (unknown2) {
            x := x + 1;
            y := y + 2;
        }
        else if (unknown3) {
            if (x >= 4) {
                x := x + 1;
                y := y + 3;
                z := z + 10;
                w := w + 10;
            }
        }
        else if (x >= z && w >= y + 1) {
            x := -x;
            y := -y;
        }
    }

    // post-condition
    assert(!(3 * x <= y - 1));
}
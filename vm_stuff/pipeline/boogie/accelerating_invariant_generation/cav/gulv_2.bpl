procedure main()
{
    var x: int;
    var y: int;
    var w: int;
    var z: int;
    var nondet: bool;

    // pre-conditions
    x := 0;
    y := 0;
    w := 0;
    z := 0;

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant y >= -100 * x;
    invariant w >= 0;
    invariant z == 10 * w;
    {
        havoc nondet;
        
        if (nondet) {
            x := x + 1;
            y := y + 100;
        }
        else if (nondet) {
            if (x >= 4) {
                x := x + 1;
                y := y + 1;
            }
        }
        else if (y > 10 * w && z >= 100 * x) {
            y := -y;
        }
        
        w := w + 1;
        z := z + 10;
        x := x; // work around VC gen bug
    }

    // post-condition
    assert(!(x >= 4 && y <= 2));
}
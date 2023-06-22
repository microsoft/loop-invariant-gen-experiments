procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var w: int;
    var nondet1: bool;
    var nondet2: bool;
    var nondet3: bool;

    // pre-conditions
    x := 0;
    y := 0;
    z := 0;
    w := 0;

    // loop body
    while (nondet1)
    invariant x >= 0;
    invariant y >= 2 * x OR (x >= 4 AND y >= 3 * x);
    invariant z >= 0;
    invariant w >= 0;
    {
        havoc nondet1;
        havoc nondet2;
        havoc nondet3;

        if (nondet2)
        {
            x := x + 1;
            y := y + 2;
        }
        else if (nondet3)
        {
            if (x >= 4)
            {
                x := x + 1;
                y := y + 3;
                z := z + 10;
                w := w + 10;
            }
        }
        else if (x >= z && w > y)
        {
            x := -x;
            y := -y;
        }
    }

    // post-condition
    assert(3 * x >= y);
}
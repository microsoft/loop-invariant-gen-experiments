procedure main()
{
    var x: int;
    var y: int;
    var z: int;
    var tmp: bool;
    var unknown_int: int;

    // pre-conditions
    x := unknown_int;
    y := unknown_int;
    z := unknown_int;
    assume(x < 100);
    assume(z < 100);

    // loop body
    while (x < 100 && 100 < z)
    invariant x < 100;
    invariant z < 100;
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
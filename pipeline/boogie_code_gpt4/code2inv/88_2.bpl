procedure main()
{
    var x: int;
    var y: int;
    var lock: int;
    var unknown: bool;

    // pre-conditions
    y := x + 1;
    lock := 0;

    // loop body
    while (x != y)
    invariant y > x;
    invariant lock == 0 || lock == 1;
    {
        havoc unknown;
        if (unknown) {
            lock := 1;
            x := y;
        } else {
            lock := 0;
            x := y;
            y := y + 1;
        }
    }

    // post-condition
    assert(lock == 1);
}
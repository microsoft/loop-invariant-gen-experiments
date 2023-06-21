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
    invariant (lock == 0) ==> (y == x + 1);
    invariant (lock == 1) ==> (y == x);
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
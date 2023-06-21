procedure main()
{
    var x: int;
    var y: int;
    var N: int;
    var nondet: bool;

    // pre-condition
    if (N < 0) {
        return;
    }

    // loop body
    while (true)
    invariant x >= 0;
    invariant y >= -1;
    invariant (x <= N) ==> (y == x);
    invariant (x >= N + 1) ==> (y == 2 * N + 1 - x);
    {
        if (x <= N) {
            y := y + 1;
        }
        else if (x >= N + 1) {
            y := y - 1;
        }
        else {
            return;
        }

        if (y < 0) {
            break;
        }
        x := x + 1;
    }

    // post-condition
    assert !((N >= 0) && (y == -1) && (x >= 2 * N + 3));
}
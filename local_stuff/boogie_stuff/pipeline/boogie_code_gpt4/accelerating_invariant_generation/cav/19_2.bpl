procedure main()
{
    var n: int;
    var m: int;
    var x: int;
    var y: int;

    // pre-conditions
    n := unknown_int();
    m := unknown_int();
    assume(n >= 0);
    assume(m >= 0);
    assume(m <= n - 1);

    x := 0;
    y := m;

    // loop body
    while (x <= n - 1)
    invariant x >= 0;
    invariant x <= n;
    invariant y >= m;
    invariant y <= m + n - x;
    {
        x := x + 1;

        if (x >= m + 1) {
            y := y + 1;
        }
        else if (x > m) {
            return;
        }
    }

    // post-condition
    if (x < n) {
        return;
    }
    assert(!(y >= n + 1));
}
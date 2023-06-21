procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    x := 0;
    m := 0;
    // n is an unknown integer, so we don't set any specific constraints on it

    // loop body
    while (x <= n - 1)
    invariant 0 <= x <= n;
    invariant 0 <= m <= x;
    {
        havoc nondet;
        if (nondet)
        {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (x >= n)
    {
        assert(!(n >= 1 && (m <= -1 || m >= n)));
    }
}
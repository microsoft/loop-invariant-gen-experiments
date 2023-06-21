procedure main()
{
    var n: int;
    var i: int;
    var sum: int;

    // pre-conditions
    assume(n >= 0);
    assume(n <= 200);

    // initialization
    i := 1;
    sum := 0;

    // loop body
    while (i <= n)
    invariant i >= 1;
    invariant sum == (i - 1) * i div 2;
    {
        sum := sum + i;
        i := i + 1;
    }

    // post-condition
    assert(sum == n * (n + 1) div 2);
}
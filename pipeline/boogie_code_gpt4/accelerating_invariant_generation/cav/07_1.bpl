procedure main()
{
    var n: int;
    var i: int;
    var j: int;

    // pre-conditions
    assume(n >= 0);

    // initialization
    i := 0;
    j := 0;

    // loop body
    while (i < n)
    invariant i == j;
    invariant i <= n;
    {
        i := i + 1;
        j := j + 1;
    }

    // post-condition
    assert(j < n + 1);
}
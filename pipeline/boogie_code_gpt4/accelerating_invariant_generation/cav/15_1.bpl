procedure main()
{
    var n: int;
    var i: int;
    var k: int;
    var j: int;
    var delta: int;

    // pre-conditions
    n := unknown_int();
    assume(n >= 1);
    assume(k >= n);

    // initialize variables
    j := 0;
    delta := k - j;

    // loop body
    while (j <= n - 1)
    invariant j >= 0;
    invariant j <= n;
    invariant delta == k - j;
    {
        j := j + 1;
        k := k - 1;
    }

    // post-conditions
    assume(j >= n);
    assert(k >= 0);
}
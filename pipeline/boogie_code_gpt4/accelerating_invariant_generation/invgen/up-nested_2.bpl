procedure main()
{
    var n: int;
    var j: int;
    var i: int;
    var k: int;

    // pre-conditions
    assume(j <= n);
    assume(i >= 0);

    // loop body
    while (j <= n)
    invariant i >= 0;
    invariant j <= n;
    {
        assume(i >= 0);
        j := j + 1;
    }

    // post-condition
    assert(i >= 0);
}
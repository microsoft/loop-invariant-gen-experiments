procedure main()
{
    var i: int;
    var j: int;

    // pre-conditions
    assume(i == 1);
    assume(j == 20);

    // loop body
    while (j >= i)
    invariant j == 20 - ((i - 1) div 2);
    {
        i := i + 2;
        j := j - 1;
    }

    // post-condition
    assert(j == 13);
}
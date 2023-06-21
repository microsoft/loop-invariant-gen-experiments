procedure main()
{
    var i: int;
    var j: int;
    var nondet: bool;

    // pre-conditions
    assume(i == 1);
    assume(j == 10);

    // loop body
    while (j >= i)
    invariant i + j == 11;
    {
        i := i + 2;
        j := j - 1;
    }

    // post-condition
    assert(j == 6);
}
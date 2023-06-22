procedure main()
{
    var i: int;
    var j: int;
    var n: int;
    var nondet: bool;

    // pre-conditions
    assume(i == 1);
    assume(j == 10);

    // loop body
    while (j >= i)
    invariant j - i == 9 - (2 * n);
    invariant n >= 0;
    {
        n := n + 1;
        i := i + 2;
        j := j - 1;
    }

    // post-condition
    assert(j == 6);
}
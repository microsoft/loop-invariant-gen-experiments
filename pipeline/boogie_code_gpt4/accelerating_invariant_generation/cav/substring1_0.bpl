procedure main()
{
    var i: int;
    var j: int;
    var from: int;
    var k: int;
    var nondet: bool;

    // pre-conditions
    assume(k >= 0);
    assume(k <= 100);
    assume(from >= 0);
    assume(from <= k);

    i := from;
    j := 0;

    // loop body
    while (i < k)
    invariant i >= from;
    invariant j >= 0;
    invariant i - from == j;
    {
        i := i + 1;
        j := j + 1;
    }

    // post-condition
    assert(j < 101);
}
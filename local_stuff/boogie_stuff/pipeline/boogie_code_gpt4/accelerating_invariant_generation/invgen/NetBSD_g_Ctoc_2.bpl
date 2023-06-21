procedure main()
{
    var BASE_SZ: int;
    var i: int;
    var j: int;
    var len: int;
    var unknown: bool;

    // pre-conditions
    assume(BASE_SZ >= 0);

    len := BASE_SZ;

    if (!(BASE_SZ > 0))
    {
        return;
    }

    assert(0 <= BASE_SZ - 1);

    if (len == 0)
    {
        return;
    }

    i := 0;
    j := 0;

    // loop body
    while (true)
    invariant 0 <= i;
    invariant i < BASE_SZ;
    invariant 0 <= j;
    invariant j < BASE_SZ;
    invariant 0 <= len;
    invariant len <= BASE_SZ;
    {
        assert(0 <= j);
        assert(j < BASE_SZ);
        assert(0 <= i);
        assert(i < BASE_SZ);

        if (unknown || len == 1)
        {
            return;
        }

        i := i + 1;
        j := j + 1;
        len := len - 1;
    }

    // post-condition
    // The loop can only terminate by encountering a return statement,
    // so there are no explicit post-conditions after the loop.
}
procedure main()
{
    var p: int;
    var i: int;
    var leader_len: int;
    var bufsize: int;
    var bufsize_0: int;
    var ielen: int;
    var nondet: bool;

    // pre-conditions
    assume(leader_len > 0);
    assume(bufsize > 0);
    assume(ielen > 0);

    if (bufsize < leader_len)
    {
        return;
    }

    p := 0;
    bufsize_0 := bufsize;
    bufsize := bufsize - leader_len;
    p := p + leader_len;

    if (bufsize < 2 * ielen)
    {
        return;
    }

    i := 0;
    while (nondet)
    invariant i >= 0;
    invariant i <= ielen;
    invariant p >= leader_len;
    invariant p <= leader_len + 2 * i;
    invariant bufsize >= bufsize_0 - leader_len - 2 * i;
    invariant bufsize <= bufsize_0 - leader_len;
    invariant 0 <= p;
    invariant p + 1 < bufsize_0;
    {
        havoc nondet;
        if (i >= ielen || bufsize <= 2) {
            break;
        }
        p := p + 2;
        i := i + 1;
    }

    // post-conditions
    assert(i >= ielen || bufsize <= 2);
    assert(p == leader_len + 2 * i);
    assert(bufsize == bufsize_0 - leader_len - 2 * i);
    assert(0 <= p);
    assert(p + 1 < bufsize_0);
}
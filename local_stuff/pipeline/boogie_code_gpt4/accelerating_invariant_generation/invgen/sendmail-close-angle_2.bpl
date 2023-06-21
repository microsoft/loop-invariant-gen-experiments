procedure main()
{
    var in: int;
    var inlen: int;
    var bufferlen: int;
    var buf: int;
    var buflim: int;
    var nondet: bool;

    // pre-conditions
    assume(bufferlen > 1);
    assume(inlen > 0);
    assume(bufferlen < inlen);

    // initialization
    buf := 0;
    in := 0;
    buflim := bufferlen - 2;

    // loop body
    while (nondet)
    invariant 0 <= buf < bufferlen;
    invariant 0 <= in < inlen;
    invariant buf == in;
    invariant buflim == bufferlen - 2;
    invariant bufferlen > 1;
    invariant inlen > 0;
    invariant bufferlen < inlen;
    {
        havoc nondet;
        if (buf == buflim)
        {
            break;
        }
        buf := buf + 1;
        in := in + 1;
    }

    // post-conditions
    assert(0 <= buf < bufferlen);
    buf := buf + 1;
    assert(0 <= buf < bufferlen);
    buf := buf + 1;
    assert(0 <= buf < bufferlen);
}
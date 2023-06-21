procedure main()
{
    var fbuflen: int;
    var fb: int;
    var unknown: bool;

    // pre-conditions
    assume(fbuflen > 0);

    fb := 0;

    // loop body
    while (unknown)
    invariant 0 <= fb;
    invariant fb < fbuflen;
    {
        havoc unknown;

        if (unknown) {
            break;
        }

        if (unknown) {
            break;
        }

        // First block
        assert(0 <= fb);
        assert(fb < fbuflen);
        fb := fb + 1;
        if (fb >= fbuflen - 1) {
            fb := 0;
        }

        // Second block
        assert(0 <= fb);
        assert(fb < fbuflen);
        fb := fb + 1;
        if (fb >= fbuflen - 1) {
            fb := 0;
        }

        // Third block
        assert(0 <= fb);
        assert(fb < fbuflen);
        fb := fb + 1;
        if (fb >= fbuflen - 1) {
            fb := 0;
        }
    }

    // post-condition
    if (fb > 0) {
        assert(0 <= fb);
        assert(fb < fbuflen);
    }
}
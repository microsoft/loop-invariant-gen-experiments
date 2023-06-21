procedure main()
{
    var MAXPATHLEN: int;
    var buf_off: int;
    var pattern_off: int;
    var bound_off: int;
    var glob3_pathbuf_off: int;
    var glob3_pathend_off: int;
    var glob3_pathlim_off: int;
    var glob3_pattern_off: int;
    var glob3_dc: int;
    var nondet: bool;

    // pre-conditions
    assume(MAXPATHLEN > 0);

    buf_off := 0;
    pattern_off := 0;
    bound_off := 0 + (MAXPATHLEN + 1) - 1;

    glob3_pathbuf_off := buf_off;
    glob3_pathend_off := buf_off;
    glob3_pathlim_off := bound_off;
    glob3_pattern_off := pattern_off;

    glob3_dc := 0;

    // loop body
    while (nondet)
    invariant glob3_dc >= 0;
    invariant glob3_dc <= MAXPATHLEN;
    invariant glob3_pathend_off + glob3_dc < glob3_pathlim_off;
    invariant MAXPATHLEN > 0;
    {
        havoc nondet;
        if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off) {
            break;
        } else {
            glob3_dc := glob3_dc + 1;
            // OK
            assert(glob3_dc > -1 && glob3_dc < MAXPATHLEN + 1);
            if (nondet) {
                return;
            }
        }
    }

    // post-condition
    assert(glob3_pathend_off + glob3_dc >= glob3_pathlim_off);
    assert(glob3_dc >= 0);
    assert(glob3_dc <= MAXPATHLEN);
    assert(MAXPATHLEN > 0);
}
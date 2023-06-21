procedure main()
{
    var MAXPATHLEN: int;
    var pathbuf_off: int;
    var bound_off: int;
    var glob2_p_off: int;
    var glob2_pathbuf_off: int;
    var glob2_pathlim_off: int;
    var nondet: bool;

    // pre-conditions
    assume(MAXPATHLEN > 0);

    // variable initialization
    pathbuf_off := 0;
    bound_off := pathbuf_off + (MAXPATHLEN + 1) - 1;
    glob2_pathbuf_off := pathbuf_off;
    glob2_pathlim_off := bound_off;
    glob2_p_off := glob2_pathbuf_off;

    // loop body
    while (nondet)
    invariant 0 <= glob2_p_off;
    invariant glob2_p_off <= MAXPATHLEN + 1;
    {
        havoc nondet;
        assert(0 <= glob2_p_off);
        assert(glob2_p_off <= MAXPATHLEN + 1);
        glob2_p_off := glob2_p_off + 1;
    }

    // post-condition
    assert(glob2_p_off == glob2_pathlim_off + 1);
}
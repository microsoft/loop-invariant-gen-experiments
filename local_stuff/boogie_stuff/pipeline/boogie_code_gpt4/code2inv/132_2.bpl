procedure main()
{
    var i: int;
    var j: int;
    var c: int;
    var t: int;
    var nondet: bool;

    // initialization
    i := 0;

    // loop body
    while (nondet)
    invariant i >= 0;
    {
        havoc nondet;
        havoc c;

        if (c > 48) {
            if (c < 57) {
                j := i + i;
                t := c - 48;
                i := j + t;
            }
        }
    }

    // post-condition
    assert(i >= 0);
}
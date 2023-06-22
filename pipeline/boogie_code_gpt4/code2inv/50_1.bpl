procedure main()
{
    var c: int;
    var nondet: bool;

    // pre-conditions
    assume(c == 0);

    // loop body
    while (nondet)
    invariant c >= 0;
    invariant c <= 4;
    {
        havoc nondet;
        if (nondet) {
            if (c != 4) {
                c := c + 1;
            }
        } else {
            if (c == 4) {
                c := 1;
            }
        }
    }

    // post-condition
    if (c != 4) {
        assert(c >= 0);
    }
}
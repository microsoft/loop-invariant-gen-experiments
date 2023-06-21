procedure main()
{
    var c: int;
    var nondet1: bool;
    var nondet2: bool;

    // pre-conditions
    assume(c == 0);

    // loop body
    while (nondet1)
    invariant c >= 0;
    invariant c <= 4;
    {
        havoc nondet1;
        havoc nondet2;

        if (nondet2) {
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
        assert(c <= 4);
    }
}
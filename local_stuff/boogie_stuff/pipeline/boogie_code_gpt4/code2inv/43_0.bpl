procedure main()
{
    var c: int;
    var n: int;
    var unknown1: bool;
    var unknown2: bool;

    // pre-conditions
    c := 0;
    assume(n > 0);

    // loop body
    while (unknown1)
    invariant c >= 0;
    invariant c >= 1 || c == 0;
    {
        havoc unknown1;
        havoc unknown2;

        if (unknown2) {
            if (c > n) {
                c := c + 1;
            }
        } else {
            if (c == n) {
                c := 1;
            }
        }
    }

    // post-condition
    if (c == n) {
        assert(n > -1);
    }
}
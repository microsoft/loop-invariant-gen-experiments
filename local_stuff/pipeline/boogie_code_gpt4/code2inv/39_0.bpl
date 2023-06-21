procedure main()
{
    var n: int;
    var c: int;
    var unknown: bool;

    // pre-conditions
    assume(n > 0);

    // loop body
    while (unknown)
    invariant 1 <= c;
    invariant c <= n;
    {
        havoc unknown;
        if (c == n) {
            c := 1;
        }
        else {
            c := c + 1;
        }
    }

    // post-condition
    if (c == n) {
        assert(c <= n);
    }
}
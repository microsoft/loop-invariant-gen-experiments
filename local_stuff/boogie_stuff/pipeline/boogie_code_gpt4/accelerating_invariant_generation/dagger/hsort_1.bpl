procedure main()
{
    var n, l, r, i, j: int;
    var unknown: bool;

    // pre-conditions
    assume(n >= 2);
    assume(r - n == 0);
    assume(i - l == 0);
    assume(j - 2*l == 0);
    assume(2*l - n >= 0);
    assume(2*l - n - 1 <= 0);

    // loop body
    while (unknown)
    invariant 2*i - j == 0;
    invariant -2*l + r >= -1;
    invariant -2*l + 3*r - 2*i >= 0;
    invariant -l + i >= 0;
    invariant r >= 2;
    invariant l >= 1;
    invariant n - r >= 0;
    {
        havoc unknown;

        if (unknown)
        {
            assume(r - j - 1 >= 0);
            i := j + 1;
            j := 2*j + 2;
        }
        else
        {
            if (unknown)
            {
                assume(j - r <= 0);
                i := j;
                j := 2*j;
            }
            else
            {
                if (unknown)
                {
                    assume(l >= 2);
                    assume(r >= 2);
                    i := l - 1;
                    j := 2*l - 2;
                    l := l - 1;
                }
                else
                {
                    assume(l <= 1);
                    r := r - 1;
                    assume(r >= 3);
                    i := l;
                    j := 2*l;
                }
            }
        }
    }

    // post-conditions
    assert(2*i - j >= 0);
    assert(2*i - j <= 0);
    assert(-2*l + r + 1 >= 0);
    assert(r - 2 >= 0);
    assert(l - 1 >= 0);
    assert(n - r >= 0);
}
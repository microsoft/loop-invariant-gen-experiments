procedure main()
{
    var n, l, r, i, j: int;
    var unknown: bool;

    // pre-conditions
    assume(n >= 2);
    assume(r == n);
    assume(i == l);
    assume(j == 2 * l);
    assume(2 * l - n >= 0);
    assume(2 * l - n - 1 <= 0);

    // loop body
    while (unknown)
    invariant 2 * i - j == 0;
    invariant -2 * l + r >= -1;
    invariant -2 * l + 3 * r - 2 * i >= 0;
    invariant -l + i >= 0;
    invariant r >= 2;
    invariant l >= 1;
    invariant n - r >= 0;
    {
        havoc unknown;
        if (unknown)
        {
            if (r - j - 1 >= 0)
            {
                i := j + 1;
                j := 2 * j + 2;
            }
        }
        else
        {
            if (unknown)
            {
                if (j - r <= 0)
                {
                    i := j;
                    j := 2 * j;
                }
            }
            else
            {
                if (unknown)
                {
                    if (l >= 2 && r >= 2)
                    {
                        i := l - 1;
                        j := 2 * l - 2;
                        l := l - 1;
                    }
                }
                else
                {
                    if (l <= 1)
                    {
                        r := r - 1;
                        if (r >= 3)
                        {
                            i := l;
                            j := 2 * l;
                        }
                    }
                }
            }
        }
    }

    // post-condition
    assert(-2 * l + r + 1 >= 0);
}
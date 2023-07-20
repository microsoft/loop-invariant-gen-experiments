procedure main()
{
    var x1, x2, x3, x4, x5, x6, x7, p, q: int;
    var unknown: bool;

    // pre-conditions
    assume(x6 == p);
    assume(x7 == q);
    assume(p >= 1);
    assume(q >= 1);

    // loop body
    while (unknown)
    invariant x1 >= 0;
    invariant x2 >= 0;
    invariant x3 >= 0;
    invariant x4 >= 0;
    invariant x5 >= 0;
    invariant x6 >= 0;
    invariant x7 >= 0;
    invariant p >= 1;
    invariant q >= 1;
    invariant x1 + x6 == p;
    invariant x2 + x3 + x4 + x7 == q;
    {
        havoc unknown;
        if (unknown)
        {
            if (x6 >= 1)
            {
                x1 := x1 + 1;
                x6 := x6 - 1;
            }
        }
        else
        {
            if (unknown)
            {
                if (x1 >= 1 && x7 >= 1)
                {
                    x1 := x1 - 1;
                    x2 := x2 + 1;
                    x7 := x7 - 1;
                }
            }
            else
            {
                if (unknown)
                {
                    if (x2 >= 1)
                    {
                        x2 := x2 - 1;
                        x3 := x3 + 1;
                        x6 := x6 + 1;
                    }
                }
                else
                {
                    if (unknown)
                    {
                        if (x3 >= 1 && x6 >= 1)
                        {
                            x3 := x3 - 1;
                            x4 := x4 + 1;
                            x6 := x6 - 1;
                        }
                    }
                    else
                    {
                        if (unknown)
                        {
                            if (x4 >= 1)
                            {
                                x4 := x4 - 1;
                                x5 := x5 + 1;
                                x7 := x7 + 1;
                            }
                        }
                        else
                        {
                            if (x5 >= 1)
                            {
                                x5 := x5 - 1;
                                x6 := x6 + 1;
                            }
                        }
                    }
                }
            }
        }
    }

    // post-conditions
    assert(x2 + x3 + x4 + x7 == q);
    assert(x1 + x2 + x4 + x5 + x6 == p);
    assert(x7 >= 0);
    assert(x6 >= 0);
    assert(x5 >= 0);
    assert(x4 >= 0);
    assert(x3 >= 0);
    assert(x2 >= 0);
    assert(x1 >= 0);
    assert(x2 + x3 + x4 + x7 >= 1);
    assert(x1 + x2 + x4 + x5 + x6 >= 1);
}
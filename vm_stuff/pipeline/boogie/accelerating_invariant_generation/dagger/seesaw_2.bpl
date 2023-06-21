procedure main()
{
    var x: int;
    var y: int;
    var nondet: bool;

    // pre-conditions
    assume(x == 0);
    assume(y == 0);

    // loop body
    while (nondet)
    invariant x >= 0;
    invariant y >= 0;
    {
        havoc nondet;

        if (nondet)
        {
            if (x >= 9)
            {
                x := x + 2;
                y := y + 1;
            }
        }
        else
        {
            if (nondet)
            {
                if (x >= 7 && x <= 9)
                {
                    x := x + 1;
                    y := y + 3;
                }
            }
            else
            {
                if (nondet)
                {
                    if (x - 5 >= 0 && x - 7 <= 0)
                    {
                        x := x + 2;
                        y := y + 1;
                    }
                }
                else
                {
                    if (x - 4 <= 0)
                    {
                        x := x + 1;
                        y := y + 2;
                    }
                }
            }
        }
    }

    // post-conditions
    assert(-x + 2*y >= 0);
    assert(3*x - y >= 0);
}
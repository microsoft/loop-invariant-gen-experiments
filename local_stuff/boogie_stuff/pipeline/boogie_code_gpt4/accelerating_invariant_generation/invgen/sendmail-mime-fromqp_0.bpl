procedure main()
{
    var outfilelen: int;
    var nchar: int;
    var out: int;
    var nondet: bool;

    // pre-conditions
    nchar := 0;
    out := 0;

    if (!(outfilelen > 0))
    {
        return;
    }

    // loop body
    while (nondet)
    invariant 0 <= out;
    invariant nchar >= 0;
    {
        havoc nondet;

        if (nondet)
        {
            if (nondet)
            {
                break;
            }

            if (nondet)
            {
                out := 0;
                nchar := 0;
                continue;
            }
            else
            {
                if (nondet)
                {
                    break;
                }

                nchar := nchar + 1;
                if (nchar >= outfilelen)
                {
                    break;
                }

                assert(0 <= out);
                assert(out < outfilelen);
                out := out + 1;
            }
        }
        else
        {
            nchar := nchar + 1;
            if (nchar >= outfilelen)
                break;

            assert(0 <= out);
            assert(out < outfilelen);
            out := out + 1;
            if (nondet)
                break;
        }
    }

    // post-condition
    assert(0 <= out);
    assert(out < outfilelen);
    out := out + 1;
}
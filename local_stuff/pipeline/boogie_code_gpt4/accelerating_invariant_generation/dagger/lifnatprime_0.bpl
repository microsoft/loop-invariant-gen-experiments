procedure main()
{
    var I: int;
    var Sa: int;
    var Ea: int;
    var Ma: int;
    var Sb: int;
    var Eb: int;
    var Mb: int;
    var nondet: bool;

    // pre-conditions
    assume(I >= 1);
    Sa := 0;
    Ea := 0;
    Ma := 0;
    Sb := 0;
    Eb := 0;
    Mb := 0;

    // loop body
    while (nondet)
    invariant I >= 1;
    invariant Ea + Ma <= 1;
    invariant Eb + Mb <= 1;
    {
        havoc nondet;
        if (nondet)
        {
            if (Eb >= 1)
            {
                Eb := Eb - 1;
                Mb := Mb + 1;
            }
        }
        else
        {
            if (nondet)
            {
                if (Ea >= 1)
                {
                    Ea := Ea - 1;
                    Ma := Ma + 1;
                }
            }
            else
            {
                if (nondet)
                {
                    if (Sa >= 1)
                    {
                        Sa := Sa - 1;
                        I := I + Sb + Eb + Mb;
                        Sb := 0;
                        Eb := 1;
                        Mb := 0;
                    }
                }
                else
                {
                    if (nondet)
                    {
                        if (Sb >= 1)
                        {
                            I := I + Sb + Eb + Mb;
                            Sb := 0;
                            Eb := 1;
                            Mb := 0;
                        }
                    }
                    else
                    {
                        if (nondet)
                        {
                            if (Sb >= 1)
                            {
                                Sb := Sb - 1;
                                I := I + Sa + Ea + Ma;
                                Sa := 0;
                                Ea := 1;
                                Ma := 0;
                            }
                        }
                        else
                        {
                            if (nondet)
                            {
                                if (Sa >= 1)
                                {
                                    I := I + Sa + Ea + Ma;
                                    Sa := 0;
                                    Ea := 1;
                                    Ma := 0;
                                }
                            }
                            else
                            {
                                if (nondet)
                                {
                                    if (Sa >= 1)
                                    {
                                        Sa := Sa - 1;
                                        Sb := Sb + Eb + Mb + 1;
                                        Eb := 0;
                                        Mb := 0;
                                    }
                                }
                                else
                                {
                                    if (nondet)
                                    {
                                        if (I >= 1)
                                        {
                                            I := I - 1;
                                            Sb := Sb + Eb + Mb + 1;
                                            Eb := 0;
                                            Mb := 0;
                                        }
                                    }
                                    else
                                    {
                                        if (nondet)
                                        {
                                            if (I >= 1)
                                            {
                                                I := I - 1;
                                                Sa := Sa + Ea + Ma + 1;
                                                Ea := 0;
                                                Ma := 0;
                                            }
                                        }
                                        else
                                        {
                                            if (Sb >= 1)
                                            {
                                                Sb := Sb - 1;
                                                Sa := Ea + Ma + 1;
                                                Ea := 0;
                                                Ma := 0;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // post-conditions
    assert(Ea + Ma <= 1);
    assert(Eb + Mb <= 1);
    assert(I + Sa + Ea + Ma + Sb + Eb + Mb >= 1);
}
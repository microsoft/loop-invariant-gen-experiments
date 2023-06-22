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
    var branch: int;

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
    invariant I >= 0;
    invariant Sa >= 0;
    invariant Ea >= 0;
    invariant Ma >= 0;
    invariant Sb >= 0;
    invariant Eb >= 0;
    invariant Mb >= 0;
    invariant Ea + Ma <= 1;
    invariant Eb + Mb <= 1;
    {
        havoc nondet;
        havoc branch;

        if (branch == 0)
        {
            assume(Sb >= 1);
            Sb := Sb - 1;
            Sa := Ea + Ma + 1;
            Ea := 0;
            Ma := 0;
        }
        else if (branch == 1)
        {
            assume(I >= 1);
            I := I - 1;
            Sa := Sa + Ea + Ma + 1;
            Ea := 0;
            Ma := 0;
        }
        else if (branch == 2)
        {
            assume(I >= 1);
            I := I - 1;
            Sb := Sb + Eb + Mb + 1;
            Eb := 0;
            Mb := 0;
        }
        else if (branch == 3)
        {
            assume(Sa >= 1);
            Sa := Sa - 1;
            Sb := Sb + Eb + Mb + 1;
            Eb := 0;
            Mb := 0;
        }
        else if (branch == 4)
        {
            assume(Sa >= 1);
            I := I + Sa + Ea + Ma;
            Sa := 0;
            Ea := 1;
            Ma := 0;
        }
        else if (branch == 5)
        {
            assume(Sb >= 1);
            Sb := Sb - 1;
            I := I + Sa + Ea + Ma;
            Sa := 0;
            Ea := 1;
            Ma := 0;
        }
        else if (branch == 6)
        {
            assume(Sb >= 1);
            I := I + Sb + Eb + Mb;
            Sb := 0;
            Eb := 1;
            Mb := 0;
        }
        else if (branch == 7)
        {
            assume(Sa >= 1);
            Sa := Sa - 1;
            I := I + Sb + Eb + Mb;
            Sb := 0;
            Eb := 1;
            Mb := 0;
        }
        else if (branch == 8)
        {
            assume(Ea >= 1);
            Ea := Ea - 1;
            Ma := Ma + 1;
        }
        else
        {
            assume(Eb >= 1);
            Eb := Eb - 1;
            Mb := Mb + 1;
        }
    }

    // post-conditions
    assert(Ea + Ma <= 1);
    assert(Eb + Mb <= 1);
    assert(Mb >= 0);
    assert(Eb >= 0);
    assert(Ma >= 0);
    assert(Ea >= 0);
}
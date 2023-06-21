procedure main()
{
    var invalid: int;
    var unowned: int;
    var nonexclusive: int;
    var exclusive: int;
    var unknown1: bool;
    var unknown2: bool;

    // pre-conditions
    assume(invalid >= 1);
    assume(unowned == 0);
    assume(nonexclusive == 0);
    assume(exclusive == 0);

    // loop body
    while (unknown1)
    invariant invalid >= 0;
    invariant unowned >= 0;
    invariant nonexclusive >= 0;
    invariant exclusive >= 0;
    {
        havoc unknown1;
        havoc unknown2;

        if (unknown2)
        {
            assume(invalid >= 1);
            nonexclusive := nonexclusive + exclusive;
            exclusive := 0;
            invalid := invalid - 1;
            unowned := unowned + 1;
        }
        else
        {
            if (unknown1)
            {
                assume(nonexclusive + unowned >= 1);
                invalid := invalid + unowned + nonexclusive - 1;
                exclusive := exclusive + 1;
                unowned := 0;
                nonexclusive := 0;
            }
            else
            {
                assume(invalid >= 1);
                unowned := 0;
                nonexclusive := 0;
                exclusive := 1;
                invalid := invalid + unowned + exclusive + nonexclusive - 1;
            }
        }
    }

    // post-conditions
    assert(exclusive >= 0);
    assert(nonexclusive >= 0);
    assert(unowned >= 0);
    assert(invalid >= 0);
    assert(invalid + unowned + exclusive >= 1);
}
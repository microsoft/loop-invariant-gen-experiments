procedure main()
{
    var exclusive: int;
    var nonexclusive: int;
    var unowned: int;
    var invalid: int;
    var unknown: bool;

    // pre-conditions
    assume(exclusive == 0);
    assume(nonexclusive == 0);
    assume(unowned == 0);
    assume(invalid >= 1);

    // loop body
    while (unknown)
    invariant exclusive >= 0;
    invariant unowned >= 0;
    invariant nonexclusive >= 0;
    invariant invalid + unowned + exclusive >= 1;
    invariant 2 * invalid + unowned + 2 * exclusive >= 1;
    {
        havoc unknown;
        if (unknown)
        {
            assume(invalid >= 1);
            nonexclusive := nonexclusive + exclusive;
            exclusive := 0;
            invalid := invalid - 1;
            unowned := unowned + 1;
        }
        else
        {
            if (unknown)
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
    assert(unowned >= 0);
    assert(invalid + unowned + exclusive + nonexclusive >= 1);
}
procedure main()
{
    var x1, v1, x2, v2, x3, v3, t: int;
    var unknown1, unknown2: bool;

    // pre-conditions
    assume(v3 >= 0);
    assume(v1 <= 5);
    assume(v1 - v3 >= 0);
    assume(2 * v2 - v1 - v3 == 0);

    x1 := 100;
    x2 := 75;
    x3 := -50;
    t := 0;

    // loop body
    while (unknown1)
    invariant v1 <= 5;
    invariant v2 + 5 >= 0;
    invariant v2 <= 5;
    invariant v3 >= 0;
    invariant 2 * v2 - v1 - v3 == 0;
    {
        havoc unknown1;
        havoc unknown2;

        assume(unknown2 == true || unknown2 == false);

        if (unknown2)
        {
            assume(2 * x2 - x1 - x3 >= 0);
            x1 := x1 + v1;
            x3 := x3 + v3;
            x2 := x2 + v2;
            v2 := v2 - 1;
            t := t + 1;
        }
        else
        {
            assume(2 * x2 - x1 - x3 <= 0);
            x1 := x1 + v1;
            x3 := x3 + v3;
            x2 := x2 + v2;
            v2 := v2 + 1;
            t := t + 1;
        }
    }

    // post-conditions
    assert(v1 <= 5);
    assert(2 * v2 + 2 * t >= v1 + v3);
    assert(5 * t + 75 >= x2);
    assert(v2 <= 6);
    assert(v3 >= 0);
    assert(v2 + 6 >= 0);
    assert(x2 + 5 * t >= 75);
    assert(v1 - 2 * v2 + v3 + 2 * t >= 0);
    assert(v1 - v3 >= 0);
}
procedure main()
{
    var a: int;
    var m: int;
    var j: int;
    var k: int;

    // loop body
    while (k < 1)
    invariant k >= 0;
    invariant k <= 1;
    invariant j == 0;
    invariant m >= a || k == 0;
    {
        if (m < a) {
            m := a;
        }
        k := k + 1;
    }

    // post-condition
    assert(a <= m);
}
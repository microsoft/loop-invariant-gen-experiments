procedure main()
{
    var a: int;
    var c: int;
    var m: int;
    var j: int;
    var k: int;

    // initialization
    j := 0;
    k := 0;

    // loop body
    while (k < c)
    invariant k >= 0;
    invariant k <= c;
    invariant m >= a || (m < a && k == 0);
    {
        if (m < a) {
            m := a;
        }
        k := k + 1;
    }

    // post-condition
    if (c > 0) {
        assert(a <= m);
    }
}
procedure main()
{
    var n: int;
    var v1: int;
    var v2: int;
    var v3: int;
    var x: int;
    var k: int;

    // pre-conditions
    x := n;

    // loop body
    k := 0;
    while (x > 0)
    invariant x == n - k;
    invariant k >= 0;
    {
        x := x - 1;
        k := k + 1;
    }

    // post-condition
    if (x != 0) {
        assert(n < 0);
    }
}
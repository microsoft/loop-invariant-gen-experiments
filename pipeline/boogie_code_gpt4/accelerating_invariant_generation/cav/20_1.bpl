procedure main()
{
    var x: int;
    var y: int;
    var k: int;
    var j: int;
    var i: int;
    var n: int;
    var m: int;
    var unknown: bool;

    // pre-conditions
    // No explicit pre-conditions given in the C code

    if ((x + y) != k)
        return;

    j := 0;
    var sum_xy: int := x + y;
    while (j <= n - 1)
    invariant j >= 0;
    invariant j <= n;
    invariant x + y == sum_xy;
    invariant m >= -1;
    invariant m <= n - 1;
    {
        if (j == i)
        {
            x := x + 1;
            y := y - 1;
        }
        else
        {
            y := y + 1;
            x := x - 1;
        }
        if (unknown)
            m := j;
        j := j + 1;
    }

    // post-conditions
    if (j < n)
        return;
    assert(!(x + y <= k - 1 || x + y >= k + 1 || (n >= 1 && ((m <= -1) || (m >= n)))));
}
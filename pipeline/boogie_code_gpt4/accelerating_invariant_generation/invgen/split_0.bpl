procedure main()
{
    var k: int;
    var b: bool;
    var i: int;
    var j: int;
    var n: int;

    // pre-conditions
    k := 100;
    n := 0;

    // loop body
    while (n < 2 * k)
    invariant i - j >= 0;
    invariant i - j <= 1;
    invariant n >= 0;
    invariant n <= 2 * k;
    {
        if (b) {
            i := i + 1;
        } else {
            j := j + 1;
        }
        b := !b;
        n := n + 1;
    }

    // post-condition
    assert(i == j);
}
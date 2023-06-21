procedure main()
{
    var k: int;
    var b: bool;
    var i: int;
    var j: int;
    var n: int;
    var d: int;

    // pre-conditions
    k := 100;
    n := 0;
    d := i - j;

    // loop body
    while (n < 2 * k)
    invariant (i - j == d && n % 2 == 0) || (i - j == d - 1 && b && n % 2 == 1) || (i - j == d + 1 && !b && n % 2 == 1);
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
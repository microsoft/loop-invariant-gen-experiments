procedure main()
{
    var z1: int;
    var z2: int;
    var z3: int;
    var x: int;
    var m: int;
    var n: int;
    var unknown: bool;

    // pre-conditions
    x := 1;
    m := 1;
    // n is uninitialized, so no pre-condition for n

    // loop body
    while (x < n)
    invariant (forall k: int :: (1 <= k < x && unknown) ==> (m >= k));
    invariant 1 <= m <= x;
    {
        if (unknown) {
            m := x;
        }
        x := x + 1;
    }

    // post-conditions
    if (n > 1) {
        assert(m < n);
        // assert(m >= 1); // Uncomment this line if you want to include the additional post-condition
    }
}
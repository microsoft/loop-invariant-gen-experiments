procedure main()
{
    var n: int;
    var m: int;
    var i: int;

    // pre-conditions
    // No explicit pre-conditions given, but n and m can have any value (garbage value)

    // Initialize i
    i := 1;

    // loop body
    while (i < n)
    invariant i >= 1;
    invariant i > 0;
    {
        if (m > 0) {
            i := 2 * i;
        }
        else {
            i := 3 * i;
        }
    }

    // post-condition
    assert(i > 0);
}
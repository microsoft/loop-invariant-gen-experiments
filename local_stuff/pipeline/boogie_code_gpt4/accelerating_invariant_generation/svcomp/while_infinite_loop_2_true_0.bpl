procedure main()
{
    var x: int;
    var nondet: bool;

    // pre-conditions
    x := 0;

    // loop body
    while (true)
    invariant x == 0;
    {
        assert(x == 0);
    }

    // post-condition
    // This part is unreachable due to the infinite loop, so no post-condition is needed.
}
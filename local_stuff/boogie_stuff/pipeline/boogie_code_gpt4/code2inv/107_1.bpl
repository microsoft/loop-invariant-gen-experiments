procedure main()
{
    var a: int;
    var m: int;
    var j: int;
    var k: int;
    var m_initial: int;

    // Store the initial value of m
    m_initial := m;

    // loop body
    while (k < 1)
    invariant k >= 0;
    invariant k <= 1;
    invariant j == 0;
    invariant m >= min(a, m_initial);
    {
        if (m < a) {
            m := a;
        }
        k := k + 1;
    }

    // post-condition
    assert(a <= m);
}
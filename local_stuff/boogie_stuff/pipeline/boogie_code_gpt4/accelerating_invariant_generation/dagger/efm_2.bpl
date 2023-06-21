procedure main()
{
    var X1: int;
    var X2: int;
    var X3: int;
    var X4: int;
    var X5: int;
    var X6: int;
    var nondet: bool;

    // pre-conditions
    assume(X1 >= 1);
    assume(X2 == 0);
    assume(X3 == 0);
    assume(X4 == 1);
    assume(X5 == 0);
    assume(X6 == 0);

    // loop body
    while (nondet)
    invariant X1 + X2 >= 1;
    invariant X3 >= 0;
    invariant X4 + X5 >= 1;
    invariant X6 >= 0;
    {
        havoc nondet;
        if (nondet) {
            assume(X1 >= 1);
            assume(X4 >= 1);
            X1 := X1 - 1;
            X4 := X4 - 1;
            X2 := X2 + 1;
            X5 := X5 + 1;
        } else {
            havoc nondet;
            if (nondet) {
                assume(X2 >= 1);
                assume(X6 >= 1);
                X2 := X2 - 1;
                X3 := X3 + 1;
            } else {
                havoc nondet;
                if (nondet) {
                    assume(X4 >= 1);
                    assume(X3 >= 1);
                    X3 := X3 - 1;
                    X2 := X2 + 1;
                } else {
                    havoc nondet;
                    if (nondet) {
                        assume(X3 >= 1);
                        X3 := X3 - 1;
                        X1 := X1 + 1;
                        X6 := X6 + X5;
                        X5 := 0;
                    } else {
                        assume(X2 >= 1);
                        X2 := X2 - 1;
                        X1 := X1 + 1;
                        X4 := X4 + X6;
                        X6 := 0;
                    }
                }
            }
        }
    }

    // post-conditions
    assert(X4 + X5 + X6 - 1 >= 0);
    assert(X4 + X5 + X6 - 1 <= 0);
    assert(X4 + X5 <= 1);
    assert(X5 >= 0);
    assert(X4 >= 0);
    assert(X3 >= 0);
    assert(X2 >= 0);
    assert(X1 + X5 >= 1);
    assert(X1 + X2 >= X4 + X5);
    assert(X1 + X2 + X3 >= 1);
}
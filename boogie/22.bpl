 procedure main()
{
    var z1,z2,z3: int;
    var x: int := 1;
    var m: int := 1;
    var n: int;
    var nondet: bool;
    while (x < n)
    invariant x >= 1 && m >= 1 && m <= x;
    {
        havoc nondet;
        if (nondet) {
            m := x;
        }
        x := x + 1;
    }

    if(n > 1) {
       //assert (m < n);
       assert (m >= 1);
    }
}
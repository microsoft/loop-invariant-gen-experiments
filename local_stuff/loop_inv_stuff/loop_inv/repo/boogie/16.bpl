 procedure main()
{
    var x: int;
    var m: int;
    var n: int;
    var nondet: bool;
    x := 0;
    m := 0;
    havoc nondet;
    while (x < n)
    invariant 0 <= x && x <= n && (x == 0 || m < x);
    {
        havoc nondet;
        if (nondet) {
            m := x;
        }
        x := x + 1;
    }

    if(n > 0) {
       //assert (m < n);
       assert (m >= 0);
    }
}
 procedure main()
     {
     var i: int;
     var n: int;
     var sn: int;
     // pre-conditions
     sn := 0;
     i := 1;
     // loop body
     while (i <= n)
     invariant i-1 == sn;
     {
     i := i + 1;
     sn := sn + 1;
     }
     // post-condition
     if(sn != 0) {
     assert(sn == n);
     }
     }
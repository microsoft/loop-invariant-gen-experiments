 procedure main()
     {
         var i: int;
         var j: int;
         var c: int;
         var t: int;
         var nondet: bool;
         i := 0;
         havoc nondet;
         while (nondet)
             invariant i >= 0;
         {
             havoc nondet;
             if (c > 48)
             {
                 if (c < 57)
                 {
                     j := i + i;
                     t := c - 48;
                     i := j + t;
                 }
             }
         }
         assert (i >= 0);
     }
 procedure main()
     {
       var x: int;
       var y: int;
       // pre-conditions
       x := 1;
       // loop body
       while (x < y)
       invariant x >= 1;
       {
         x := x + x;
       }
       // post-condition
       assert(x >= 1);
     }
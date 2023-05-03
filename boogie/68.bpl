 procedure main()
     {
         var n: int;
         var y: int;
         var x: int;
         x := 1;
         while (x <= n)
         invariant x >= 1 && x <= n + 1;
         {
             y := n - x;
             x := x + 1;
         }
         if (n > 0) {
             //assert (y >= 0);
             assert (y <= n);
         }
     }
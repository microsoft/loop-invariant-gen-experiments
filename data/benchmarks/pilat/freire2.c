/* algorithm for finding the closest integer to the cubic root, from www.pedrofreire.com/crea2_en.htm? */

int cubic (float a)
pre( a>0 );
   {
   float x,s;
   int r;

   x=a;
   r=1;
   s=3.25;

   inv(   4*r^3 - 6*r^2 + 3*r + 4*x - 4*a == 1   &&   x>0   &&   -12*r^2 + 4*s== 1   );
   while ( x-s > 0)
      {
      x=x-s;
      s=s+6*r+3;
      r=r+1;
      }

   return r;
   }
post(    4*r^3+6*r^2+3*r >= 4*a    &&   4*a > 4*r^3-6*r^2+3*r-1     );
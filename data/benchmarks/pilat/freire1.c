/* algorithm for finding the closest integer to the square root, from  www.pedrofreire.com/crea2_en.htm?*/

int sqrt ( float a )
pre( a > 0 );
   {
   float x;
   int r;

   x=a/2;
   r=0;

   inv( a == 2*x + r^2 - r   &&   x>0 );
   while( x>r )
      {
      x=x-r;
      r=r+1;
      }
   return r;
   }
post( result^2 + result >= a  &&  result^2 - result < a );
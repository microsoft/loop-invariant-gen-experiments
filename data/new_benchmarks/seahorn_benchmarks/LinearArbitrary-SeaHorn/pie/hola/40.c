#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();

void main( int flag)
{
   int i, j, k;
   j = 1;
   if(flag) {i=0;}
   else {i=1;}
   

   while(unknown1()) {
      i+=2;
      if(i%2 == 0) {
	j+=2;
      }
      else j++;
   } 
   
   int a = 0;
   int b=0;
   
   while(unknown2()) {
      a++;      
      b+=(j-i); 
   }
   if(flag)
     sassert(a==b);
}


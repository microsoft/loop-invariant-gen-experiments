#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

/*
 * Based on "Property-Directed Incremental Invariant Generation" by Bradley et al.
 */

int main() {
   int j = 2; 
   int k = 0;

   int flag = unknown2();

   while(unknown1()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   if(k!=0)
     sassert(j==2*k+2);

   return 0;
}

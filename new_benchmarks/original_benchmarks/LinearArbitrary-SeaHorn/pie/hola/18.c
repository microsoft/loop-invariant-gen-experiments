#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();

/*
 * Adapted from ex17.c in NECLA test suite
 */

int main() {
   int flag = unknown1();
   int a = unknown2();
   int b = unknown3();
   int j = 0;

   for (b=0; b < 100 ; ++b){
      if (flag)
         j = j +1;
   }


   if(flag)
      sassert(j==100);
}

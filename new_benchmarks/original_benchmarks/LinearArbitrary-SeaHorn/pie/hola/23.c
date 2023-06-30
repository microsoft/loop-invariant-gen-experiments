#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * ex49 from NECLA Static Analysis Benchmarks
 */


int main(){
   int i, sum=0;
   int n = unknown1();
   if( n >= 0){

   for (i=0; i < n; ++i)
      sum = sum +i;

   sassert(sum >= 0);
   }
}


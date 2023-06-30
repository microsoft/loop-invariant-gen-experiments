#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * Adapted from "Automated Error Diagnosis Using Abductive Inference" by Dillig et al.
 */

int main() {
   int n = unknown1();
   int flag = unknown1();

   if(n>=0){
   int k = 1;
   if(flag) {
	k = unknown1();
	if(k>=0) ; else return 0;
   }
   int i = 0, j = 0;
   while(i <= n) {
     i++;
     j+=i;
   }
   int z = k + i + j;
   sassert(z > 2*n);
   }
   return 0;
}


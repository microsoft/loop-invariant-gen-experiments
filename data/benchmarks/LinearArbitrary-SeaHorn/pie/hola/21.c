#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();

/*
 * Based on "larg_const.c" from InvGen test suite  
 */

int main() {
  int c1 = 4000;
  int c2 = 2000;
  int n, v;
  int i, k, j;


  n = unknown1();

  __VERIFIER_assume (n > 0 && n < 10);

  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    if(unknown2() % 2 == 0) 
      v = 0;
    else v = 1;
    
    if( v == 0 )
      k += c1;
    else 
      k += c2;
  }
  
  sassert(k>n);
  return 0;
}


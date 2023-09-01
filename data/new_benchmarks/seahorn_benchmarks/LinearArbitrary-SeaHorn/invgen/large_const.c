//#include <stdio.h>
//#include <stdlib.h>
#include "seahorn/seahorn.h"

extern int unknown();

int main(int argc, char* argv[]) {
  int c1 = unknown();
  int c2 = unknown();
  int c3 = unknown();
  int n, v;
  int i, k, j;

  __VERIFIER_assume(0 < c1 && c1 < 4000);
  __VERIFIER_assume(0 < c2 && c2 < 2000);
  __VERIFIER_assume(0 < c3 && c3 < 10000);

  if (argc == 2) 
    srandom(atoi(argv[1]));
  else {
    printf("Usage: randomseed\n");
    return -1;
  }

  n = random() % 10;

  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    v = random() % 2;
    if( v == 0 )
      k += c1;
    else if( v == 1 )
      k += c2;
    else
      k += c3;
  }

  j = 0;
  while( j < n ) {
    sassert(k > 0);
    j++;
    k--;
  }

  return 0;
}

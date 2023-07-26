#include "seahorn/seahorn.h"
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * from Invgen test suite
 */

int main() {

  int n;
  int i, k, j;

  n = unknown1();
  i = unknown1();
  k = unknown1();
  j = unknown1();

  if (n > 0 && k > n) {
  j = 0;
  while( j < n ) {
    j++;
    k--;
  } 
  sassert(k>=0);
  }
  return 0;
}

#include "seahorn/seahorn.h"

/*
 * "split.c" from InvGen benchmark suite
 */

extern int unknown();

void main() {
  int k = 100;
  int b = 0;
  int i = unknown();
  int j = unknown();
  int n;
  i = j = 0;
  for( n = 0 ; n < 2*k ; n++ ) {
    if((int )b == 1) {
      i++;
      b = 0;
    } else if ((int )b == 0) {
      j++;
      b = 1;
    } 
    //b = !b;
  }
  sassert(i == j);
}

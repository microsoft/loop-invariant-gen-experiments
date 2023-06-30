#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int n0, n1;
  int i0 = 0;
  int k = 0;
  n0 = unknown();
  n1 = unknown();

  while( i0 < n0 ) {
    i0++;
    k++;
  }
  int i1 = 0;
  while( i1 < n1 ) {
    i1++;
    k++;
  }
  int j1 = 0;
  while( j1 < n0 + n1 ) {
    if(k <= 0) sassert(0);    
    j1++;
    k--;
  }
}

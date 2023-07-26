#include "seahorn/seahorn.h"

extern int unknown();

int main() {
  int i0 = 0;
  int k = 0;
  int n0 = unknown();
  int n1 = unknown();

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
  while( j1 < n1 ) {
    if(k <= 0) sassert(0);
    j1++;
    k--;
  }
  int j0 = 0;
  while( j0 < n0 ) {
    if(k <= 0) sassert(0);
    j0++;
    k--;
  }
  //sassert (k == 0);
  return 0;
}

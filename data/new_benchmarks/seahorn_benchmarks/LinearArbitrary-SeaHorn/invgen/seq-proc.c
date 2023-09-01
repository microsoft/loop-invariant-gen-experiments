#include "seahorn/seahorn.h"

extern int unknown ();

int main(int argc, char *argv[]) {
  int n0, n1;
  n0 = unknown();
  n1 = unknown();

  int i0 = 0;
  int k = 0;
  while( i0 < n0 ) {
    i0++;
    k++;
  }
  int i1 = 0;
  while( i1 < n1 ) {
    i0--;
    i1++;
    k++;
  }
  int j1 = 0;
  while( j1 < n1 ) {
    if(k <= 0) sassert(0);
    j1++;//i0++;i1++;
    k--;
  }
  int j0 = 0;
  while( j0 < n0 ) {
    if(k <= 0) sassert(0);
    j0++;//j1++;i0++;i1++;
    k--;
  }

  //  assert( n0 + n1 <= i0 );
  return 0;
}

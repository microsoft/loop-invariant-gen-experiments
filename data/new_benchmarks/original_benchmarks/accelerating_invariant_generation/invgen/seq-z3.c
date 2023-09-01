
#include "myassert.h"

void main() {
  int n0, n1;
  int i = 0;
  int k = 0;

  while( i < 20*n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < 20*n0 ) {
    __VERIFIER_assert(k > 0);
    i++;
    k--;
  }
  return 0;
}

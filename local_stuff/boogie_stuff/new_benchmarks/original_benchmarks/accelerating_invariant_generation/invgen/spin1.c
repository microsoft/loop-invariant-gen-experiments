#include "myassert.h"

int m,k;

void main() {
  int x,j;
  acquire(m); // assume(m=0 /\ m'=1);
  x = 0;
  j = 0;
  k = 1;
  x = 1;
  __VERIFIER_assert(x>=j);
  release(m); // assume(m'=0);
}

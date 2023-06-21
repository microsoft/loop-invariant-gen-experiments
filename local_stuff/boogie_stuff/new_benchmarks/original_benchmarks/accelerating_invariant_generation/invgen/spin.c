#include "myassert.h"

int m,y;

void main() {
  int x;
  acquire(m); // assume(m=0 /\ m'=1);
  x = 0;
  y = 0;
  x = 1;
  __VERIFIER_assert(x>=1);
  release(m); // assume(m'=0);
}

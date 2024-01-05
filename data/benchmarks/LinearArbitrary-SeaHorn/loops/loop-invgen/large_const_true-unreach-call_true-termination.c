#include "assert.h"

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

  n = __VERIFIER_nondet_int();
  if (!(0 <= n && n < 10)) return 0;

  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    v = __VERIFIER_nondet_int();
    if (!(0 <= v && n < 2)) return 0;
    if( v == 0 )
      k += c1;
    else if( v == 1 )
      k += c2;
    else
      k += c3;
  }

  j = 0;
  while( j < n ) {
    __VERIFIER_assert(k > 0);
    j++;
    k--;
  }

  return 0;
}

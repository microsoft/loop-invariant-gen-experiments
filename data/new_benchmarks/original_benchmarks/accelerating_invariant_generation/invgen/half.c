#include <stdio.h>
#include "myassert.h"

int main(int argc, int *argv[]) {
  int n,i,k;

  assume(n>=0);
  k = n;
  i = 0;
  while( i < n ) {
    tmpl("(le(i,j,k,n),le(i,j,k,n))");
    k--;
    i = i + 2;
  }

  int j = 0;
 
  while( j < n/2 ) {
    tmpl("(le(i,j,k,n),le(i,j,k,n))");
    __VERIFIER_assert(k > 0);
    k--;
    j++;
  }
  return 0;
}

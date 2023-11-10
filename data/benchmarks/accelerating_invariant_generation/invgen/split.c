#include "myassert.h"

void main() {
  int k = 100;
  int b;
  int i;
  int j;
  int n;
  i = j;
  for( n = 0 ; n < 2*k ; n++ ) {
    tmpl("(le(k,b,i,j,n),le(k,b,i,j,n))");    
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
  __VERIFIER_assert(i == j);
}

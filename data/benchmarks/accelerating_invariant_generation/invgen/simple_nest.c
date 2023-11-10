#include "myassert.h"

void main() {
  int n,m;
  int i = 1;
  // tmpl("(le(i,j,k,n),le(i,j,k,n))");
   //  tmpl("(le(i,j,k,n),le(i,j,k,n),le(i,j,k,n))");
  m = 10;
  while( i < n ) {
    while( m > 0 ) {
      m--;
      i = 2*i;
    }
  }
  __VERIFIER_assert(i > 0 );
}

#include "seahorn/seahorn.h"

void main() {
  int n,m;
  n = unknown();
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
 sassert (i > 0 );
}

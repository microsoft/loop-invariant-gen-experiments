#include "seahorn/seahorn.h"

void main() {
  int n,m;
  n = unknown ();
  m = unknown ();
  int i = 1;
   //tmpl("(le(i,j,k,n),le(i,j,k,n))");
   //  tmpl("(le(i,j,k,n),le(i,j,k,n),le(i,j,k,n))");

  while( i < n ) {
    if( m > 0 ) {
      i = 2*i;
    } else {
      i = 3*i;
    }
    
  }
  sassert (i > 0 );
}

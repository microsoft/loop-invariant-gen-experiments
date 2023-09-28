#include "myassert.h"

void main() {
  int x=0;
  int n;
  
  assume(n > 0 );
  while( x < n ){
    x++;
  }
  __VERIFIER_assert( x<=n );
}

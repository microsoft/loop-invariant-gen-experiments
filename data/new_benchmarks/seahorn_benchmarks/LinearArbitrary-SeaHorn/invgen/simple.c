#include "seahorn/seahorn.h"

void main() {
  int x=0;
  int n = unknown();
  
  __VERIFIER_assume(n > 0 );
  while( x < n ){
    x++;
  }
  sassert( x<=n );
}

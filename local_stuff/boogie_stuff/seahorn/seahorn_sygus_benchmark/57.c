#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int c = unknown();
int n = unknown();
int v1 = unknown();
int v2 = unknown();
int v3 = unknown();
  // pre-conditions
  (c = 0);
  assume((n > 0));
  // loop body
  while (unknown()) {
    {
      if ( unknown() ) {
        if ( (c > n) )
        {
        (c  = (c + 1));
        }
      } else {
        if ( (c == n) )
        {
        (c  = 1);
        }
      }

    }

  }
  // post-condition
if ( (n > -1) )
sassert( (c != n) );

}

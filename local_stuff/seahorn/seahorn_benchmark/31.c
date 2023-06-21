#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int n = unknown();
int v1 = unknown();
int v2 = unknown();
int v3 = unknown();
int x = unknown();
  // pre-conditions
  (x = n);
  // loop body
  while ((x > 1)) {
    {
    (x  = (x - 1));
    }

  }
  // post-condition
if ( (x != 1) )
sassert( (n < 0) );

}

#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int n = unknown();
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
if ( (n >= 0) )
sassert( (x == 1) );

}

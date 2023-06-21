#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int n = unknown();
int x = unknown();
  // pre-conditions
  (x = 0);
  // loop body
  while ((x < n)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
if ( (n >= 0) )
sassert( (x == n) );

}

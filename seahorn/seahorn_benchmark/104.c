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
  (x = 0);
  // loop body
  while ((x < n)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
if ( (x != n) )
sassert( (n < 0) );

}
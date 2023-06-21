#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int j = unknown();
int x = unknown();
int y = unknown();
int z1 = unknown();
int z2 = unknown();
int z3 = unknown();
  // pre-conditions
  (i = x);
  (j = y);
  // loop body
  while ((x != 0)) {
    {
    (x  = (x - 1));
    (y  = (y - 1));
    }

  }
  // post-condition
if ( (i == j) )
sassert( (y == 0) );

}

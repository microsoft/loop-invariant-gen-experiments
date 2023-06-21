#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int x = unknown();
int y = unknown();
int z1 = unknown();
int z2 = unknown();
int z3 = unknown();
  // pre-conditions
  assume((x >= 0));
  assume((x <= 2));
  assume((y <= 2));
  assume((y >= 0));
  // loop body
  while (unknown()) {
    {
    (x  = (x + 2));
    (y  = (y + 2));
    }

  }
  // post-condition
if ( (y == 0) )
sassert( (x != 4) );

}

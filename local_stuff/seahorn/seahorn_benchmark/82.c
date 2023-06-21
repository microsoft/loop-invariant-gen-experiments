#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int x = unknown();
int y = unknown();
int z1 = unknown();
int z2 = unknown();
int z3 = unknown();
  // pre-conditions
  (i = 0);
  assume((x >= 0));
  assume((y >= 0));
  assume((x >= y));
  // loop body
  while (unknown()) {
    if ( (i < y) )
    {
    (i  = (i + 1));
    }

  }
  // post-condition
if ( (i >= x) )
if ( (0 > i) )
sassert( (i >= y) );

}

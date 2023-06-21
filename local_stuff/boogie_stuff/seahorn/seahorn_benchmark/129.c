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
  (x = 1);
  // loop body
  while ((x < y)) {
    {
    (x  = (x + x));
    }

  }
  // post-condition
sassert( (x >= 1) );
}

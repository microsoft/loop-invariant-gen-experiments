#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int x = unknown();
int y = unknown();
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

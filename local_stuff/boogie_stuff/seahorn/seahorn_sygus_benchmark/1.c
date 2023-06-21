#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int x = unknown();
int y = unknown();
  // pre-conditions
  (x = 1);
  (y = 0);
  // loop body
  while ((y < 100000)) {
    {
    (x  = (x + y));
    (y  = (y + 1));
    }

  }
  // post-condition
sassert( (x >= y) );
}

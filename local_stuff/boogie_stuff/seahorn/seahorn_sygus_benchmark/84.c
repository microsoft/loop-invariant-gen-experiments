#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int x = unknown();
int y = unknown();
  // pre-conditions
  (x = -50);
  // loop body
  while ((x < 0)) {
    {
    (x  = (x + y));
    (y  = (y + 1));
    }

  }
  // post-condition
sassert( (y > 0) );
}

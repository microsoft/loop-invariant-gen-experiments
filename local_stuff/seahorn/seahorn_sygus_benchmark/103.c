#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int x = unknown();
  // pre-conditions
  (x = 0);
  // loop body
  while ((x < 100)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
sassert( (x == 100) );
}

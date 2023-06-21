#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int n = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  assume((n >= 0));
  (x = n);
  (y = 0);
  // loop body
  while ((x > 0)) {
    {
    (y  = (y + 1));
    (x  = (x - 1));
    }

  }
  // post-condition
sassert( (y == n) );
}

#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int n = unknown();
int x = unknown();
  // pre-conditions
  (x = 0);
  assume((n >= 0));
  // loop body
  while ((x < n)) {
    {
    (x  = (x + 1));
    }

  }
  // post-condition
sassert( (x == n) );
}

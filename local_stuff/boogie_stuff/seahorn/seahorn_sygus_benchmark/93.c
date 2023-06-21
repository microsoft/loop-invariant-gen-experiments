#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int n = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  assume((n >= 0));
  (i = 0);
  (x = 0);
  (y = 0);
  // loop body
  while ((i < n)) {
    {
    (i  = (i + 1));
      if ( unknown() ) {
        {
        (x  = (x + 1));
        (y  = (y + 2));
        }
      } else {
        {
        (x  = (x + 2));
        (y  = (y + 1));
        }
      }

    }

  }
  // post-condition
sassert( ((3 * n) == (x + y)) );
}

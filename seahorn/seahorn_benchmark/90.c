#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int lock = unknown();
int v1 = unknown();
int v2 = unknown();
int v3 = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  (y = (x + 1));
  (lock = 0);
  // loop body
  while ((x != y)) {
    {
      if ( unknown() ) {
        {
        (lock  = 1);
        (x  = y);
        }
      } else {
        {
        (lock  = 0);
        (x  = y);
        (y  = (y + 1));
        }
      }

    }

  }
  // post-condition
sassert( (lock == 1) );
}

#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int lock = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  (x = y);
  (lock = 1);
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

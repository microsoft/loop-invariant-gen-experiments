#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int c = unknown();
int y = unknown();
int z = unknown();
  // pre-conditions
  (c = 0);
  assume((y >= 0));
  assume((y >= 127));
  (z = (36 * y));
  // loop body
  while (unknown()) {
    if ( (c < 36) )
    {
    (z  = (z + 1));
    (c  = (c + 1));
    }

  }
  // post-condition
if ( (z < 0) )
if ( (z >= 4608) )
sassert( (c >= 36) );

}

#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  (i = 0);
  assume((x >= 0));
  assume((y >= 0));
  assume((x >= y));
  // loop body
  while (unknown()) {
    if ( (i < y) )
    {
    (i  = (i + 1));
    }

  }
  // post-condition
if ( (i < y) )
sassert( (0 <= i) );
}

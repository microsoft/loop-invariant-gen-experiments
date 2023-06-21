#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int j = unknown();
int x = unknown();
int y = unknown();
  // pre-conditions
  (j = 0);
  (i = 0);
  (y = 1);
  // loop body
  while ((i <= x)) {
    {
    (i  = (i + 1));
    (j  = (j + y));
    }

  }
  // post-condition
if ( (i != j) )
sassert( (y != 1) );

}

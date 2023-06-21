#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int sn = unknown();
int v1 = unknown();
int v2 = unknown();
int v3 = unknown();
int x = unknown();
  // pre-conditions
  (sn = 0);
  (x = 0);
  // loop body
  while (unknown()) {
    {
    (x  = (x + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != -1) )
sassert( (sn == x) );

}

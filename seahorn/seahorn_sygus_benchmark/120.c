#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int sn = unknown();
  // pre-conditions
  (sn = 0);
  (i = 1);
  // loop body
  while ((i <= 8)) {
    {
    (i  = (i + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != 8) )
sassert( (sn == 0) );

}
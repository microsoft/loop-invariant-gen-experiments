#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int n = unknown();
int sn = unknown();
  // pre-conditions
  (sn = 0);
  (i = 1);
  // loop body
  while ((i <= n)) {
    {
    (i  = (i + 1));
    (sn  = (sn + 1));
    }

  }
  // post-condition
if ( (sn != n) )
sassert( (sn == 0) );

}
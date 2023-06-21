#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int j = unknown();
  // pre-conditions
  (i = 1);
  (j = 20);
  // loop body
  while ((j >= i)) {
    {
    (i  = (i + 2));
    (j  = (j - 1));
    }

  }
  // post-condition
sassert( (j == 13) );
}

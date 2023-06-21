#include "seahorn/seahorn.h"
extern int unknown();
int main() {
  // variable declarations
int i = unknown();
int j = unknown();
int k = unknown();
int n = unknown();
  // pre-conditions
  assume((k >= 0));
  assume((n >= 0));
  (i = 0);
  (j = 0);
  // loop body
  while ((i <= n)) {
    {
    (i  = (i + 1));
    (j  = (j + i));
    }

  }
  // post-condition
sassert( ((i + (j + k)) > (2 * n)) );
}

#include "myassert.h"

int main(void) {
  unsigned int x;

  while (x < 0x0fffffff) {
    x++;
  }

  __VERIFIER_assert(x >= 0x0fffffff);
}

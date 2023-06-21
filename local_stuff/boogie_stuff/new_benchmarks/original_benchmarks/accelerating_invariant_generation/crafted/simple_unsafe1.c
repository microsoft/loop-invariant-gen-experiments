#include "myassert.h"

int main(void) {
  unsigned int x = 0;

  while (x < 0x0fffffff) {
    x += 2;
  }

  __VERIFIER_assert(x % 2);
}

#include "myassert.h"

int main(void) {
  unsigned int x = 0x0ffffff0;

  while (x > 0) {
    x -= 2;
  }

  __VERIFIER_assert(!(x % 2));
}

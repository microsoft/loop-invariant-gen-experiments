#include "myassert.h"

int main(void) {
  unsigned int x = 0x0ffffff1;

  while (x > 1) {
    x -= 2;
  }

  __VERIFIER_assert(!(x % 2));
}

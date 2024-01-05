#include "myassert.h"

int main(void) {
  unsigned int x = 10;

  while (x >= 10) {
    x += 2;
  }

  __VERIFIER_assert(x % 2);
}

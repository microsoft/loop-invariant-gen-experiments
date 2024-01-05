#include "myassert.h"

int main(void) {
  unsigned int x = 0;
  unsigned short N;

  while (x < N) {
    x += 2;
  }

  __VERIFIER_assert(!(x % 2));
}

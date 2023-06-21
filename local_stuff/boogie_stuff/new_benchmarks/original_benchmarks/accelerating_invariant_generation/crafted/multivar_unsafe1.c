#include "myassert.h"

int main(void) {
  unsigned int x;
  unsigned int y = x + 1;

  while (x < 100) {
    x++;
    y++;
  }

  __VERIFIER_assert(x == y);
}

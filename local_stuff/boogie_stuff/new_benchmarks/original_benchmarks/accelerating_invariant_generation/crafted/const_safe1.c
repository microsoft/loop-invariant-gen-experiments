#include "myassert.h"

int main(void) {
  unsigned int x = 1;
  unsigned int y = 0;

  while (y < 10) {
    x = 0;
    y++;
  }

  __VERIFIER_assert(x == 0);
}

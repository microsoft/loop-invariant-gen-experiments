#include "myassert.h"

int main(void) {
  unsigned int x = 0;
  unsigned int y;

  while (x < 99) {
    if (y % 2 == 0) {
      x++;
    } else {
      x += 2;
    }
  }

  __VERIFIER_assert((x % 2) == (y % 2));
}
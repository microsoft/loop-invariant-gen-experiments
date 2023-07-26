#include "seahorn/seahorn.h"

int main(int argc, char* argv[]) {
  int i, j, x, y;

  x = 0;
  y = 0;
  i = 0;
  j = 0;

  while (unknown1()) {
    while (unknown2()) {
      if (x == y)
        i++;
      else
        j++;
    }

    if (i >= j) {
      x++;
      y++;
    } else
      y++;
  }

  sassert(i > j - 1);
  return 0;
}

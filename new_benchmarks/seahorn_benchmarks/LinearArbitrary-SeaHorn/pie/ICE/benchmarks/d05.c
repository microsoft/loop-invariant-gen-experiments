#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int x, y, i, j, flag;

  x = 0;
  y = 0;
  j = 0;
  i = 0;

  flag = unknown ();

  while (unknown1()) {
    x++;
    y++;
    i += x;
    j += y;
    if (flag != 0) j += 1;
    j = j;
  }

  sassert(j > i - 1);
}

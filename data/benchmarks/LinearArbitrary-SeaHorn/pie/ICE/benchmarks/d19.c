#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int x, y, n, m;

  n = unknown ();
  if (n >= 0) {

  m = unknown ();
  if (m >= 0 && m < n) {

  x = 0;
  y = m;

  while (x < n) {
    x++;
    if (x >= m + 1)
      y++;
    x = x;
  }

  sassert(y < n + 1);
  }
  }
}

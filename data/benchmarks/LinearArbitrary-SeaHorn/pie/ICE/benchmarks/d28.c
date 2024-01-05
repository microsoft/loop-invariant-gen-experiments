#include "seahorn/seahorn.h"

int main(int argc, char* argv[]) {
  int n, x, y;

  x = 0;
  y = 0;
  n = 0;

  while (unknown1()) {
    x++;
    y++;
  }

  while (x <= n - 1 || x >= n + 1) {
    x--;
    y--;
  }

  sassert(x != n || y == n);
  return 0;
}

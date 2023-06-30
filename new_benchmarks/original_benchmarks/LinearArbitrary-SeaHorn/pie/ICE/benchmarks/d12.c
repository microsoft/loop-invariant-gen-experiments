#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int a, b, x, y, s, t, flag;

  x = unknown();
  y = unknown();
  flag = unknown();

  t = 0;
  s = 0;
  a = 0;
  b = 0;

  while (unknown1()) {
    a++;
    b++;
    s += a;
    t += b;
    if (flag != 0) {
      t += a;
    }
    t = t;
  }

  // 2s >= t
  x = 1;
  if (flag != 0) {
    x = t - 2 * s + 2;
  }

  // x <= 2
  y = 0;
  while (y <= x) {
    if (unknown2())
      y++;
    else
      y += 2;
    y = y;
  }

  sassert(y < 5);
  return 0;
}

#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int x, y;

  x = 1;
  y = 1;

  while (unknown1()) {
    int t1 = x;
    int t2 = y;
    x = t1 + t2;
    y = t1 + t2;
  }
  

  sassert(y >= 1);
}

#include "seahorn/seahorn.h"

int main(int argc, char * argv[]) {
  int n = unknown ();
  if(n >= 0) {

  int x = n;
  int y = 0;

  while (x > 0) {
    x--;
    y++;
  }

  sassert(y == n);
  }
}

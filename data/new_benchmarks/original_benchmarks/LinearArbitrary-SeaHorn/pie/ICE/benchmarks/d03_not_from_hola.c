#include "seahorn/seahorn.h"

extern int unknown ();
extern int unknown1 ();

int main(int argc, char * argv[]) {
  int k = 1;
  int w = 1;

  while (unknown1()) {
    if (unknown()) w++;
    k += w;
  }

  sassert(k > 0);
}

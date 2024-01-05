#include "seahorn/seahorn.h"
extern int unknown1();


/*
 * From CAV'12 by Sharma et al.
 */

void main() {
  int x=0;
  int y=0;
  int n = 0;
  while(unknown1()) {
      x++;
      y++;
  }
  while(x!=n) {
      x--;
      y--;
  }
  sassert(y==n);
}

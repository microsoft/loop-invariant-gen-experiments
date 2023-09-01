#include "myassert.h"

void main() {
  int i;
  int j;
  int x = i;
  int y = j;
  while(x!=0) {
	x--;
	y--;
  }
  if(i==j)
	if(y != 0) __VERIFIER_assert(0);
}

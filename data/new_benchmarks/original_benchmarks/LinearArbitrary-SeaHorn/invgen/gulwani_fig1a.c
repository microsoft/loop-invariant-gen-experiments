#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int x,y;
  y = unknown();
  x = -50;
  while( x < 0 ) {
	x = x+y;
	y++;
  }
  sassert(y>0);
}

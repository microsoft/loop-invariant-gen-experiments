#include "seahorn/seahorn.h"

extern int unknown1();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

void main() {
  int x,y;

  x = -50;
  //y = unknown1();

  while( x < 0 ) {
	x = x+y;
	y++;
  }
  sassert(y>0);
}


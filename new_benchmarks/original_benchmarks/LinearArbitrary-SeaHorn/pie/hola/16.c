#include "seahorn/seahorn.h"
extern int unknown1();


/*
 * From "A Practical and Complete Approach to Predicate Refinement" by McMillan TACAS'06
 */

int main() {

  int i = unknown1();
  int j = unknown1();
  
  int x = i;
  int y = j;
 
  while(x!=0) {
	x--;
	y--;
  }
  if(i==j)
	sassert(y==0);
}


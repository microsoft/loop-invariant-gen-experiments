#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();

/*
 * Taken from "Counterexample Driven Refinement for Abstract Interpretation" (TACAS'06) by Gulavani
 */

void main() {
  int x= 0;
  int m=0;
  int n = unknown1();
  while(x<n) {
     if(unknown2()) {
	m = x;
     }
     x= x+1;
  }
  if(n>0) sassert(0<=m && m<n);
}

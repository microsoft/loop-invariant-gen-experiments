#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * InvGen, CAV'09 paper, fig 2
 */

void main() {
  int n = unknown1();
  int x= 0;
  while(x<n) {
    x++;
  } 
  if(n>0) sassert(x==n);
}

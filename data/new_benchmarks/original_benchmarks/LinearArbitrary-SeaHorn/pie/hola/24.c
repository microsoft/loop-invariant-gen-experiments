#include "seahorn/seahorn.h"
/*
 * "nested5.c" from InvGen test suite
 */

extern int unknown();

void main() {
  int i,j,k,n;

  n = unknown();
  
  for (i=0;i<n;i++)
    for (j=i;j<n;j++)
      for (k=j;k<n;k++)
	sassert(k>=i);
}

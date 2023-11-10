#include "seahorn/seahorn.h"
extern int unknown1();

void main()
{
 int k=1;
 int i=1;
 int j=0;
 int n = unknown();
 while(i<n) {
  j=0;
  while(j<i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 sassert(k>=n);
 
}

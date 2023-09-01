#include "seahorn/seahorn.h"

/*
 * From "Simplifying Loop Invariant Generation using Splitter Predicates", Sharma et al. CAV'11
 */
extern int unknown1();

void main()
{
  int n = unknown1 (); 
  int m = unknown1 ();
  if (n >= 0 && m >= 0 && m < n) {
  int x=0; 
  int y=m;
  while(x<n) {
    x++;
    if(x>m) y++;
  }
  sassert(y==n);
  }
}

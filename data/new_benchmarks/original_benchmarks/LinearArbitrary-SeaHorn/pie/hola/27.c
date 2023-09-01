#include "seahorn/seahorn.h"
extern int unknown1 ();
/*
 * "nested2.c" from InvGen benchmark suite
 */


void main() {
  int i,k,n,l;
  n = unknown1();
  l = unknown1();
  if(l>0) {

  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {

    }
    for (i=l;i<n;i++) {
      sassert(1<=k);
    }
  }
  }
}

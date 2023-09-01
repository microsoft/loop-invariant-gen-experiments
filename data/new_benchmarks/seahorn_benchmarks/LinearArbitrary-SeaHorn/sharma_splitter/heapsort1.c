#include "seahorn/seahorn.h"

extern int unknown();

int main() {
  int n,l,r,i,j;
  n = unknown();
  
  if(1 <= n) {
  l = n + 1;
  n=n+n;
  r = n;
  if(l>1) {
    l--;
  } else {
    r--;
  }
  while(r > 1) {
    i = l;
    j = 2*l;
    while(j <= r) {
      if( j < r) {
	sassert(1 <= j);sassert(j <= n);
	sassert(1 <= j+1);sassert(j+1 <= n);
	if( unknown() )
	  j = j + 1;
      }
      sassert(1 <= j);sassert(j <= n);
      if( unknown() ) { 
      	break;
      }
      sassert(1 <= i);
      sassert(i <= n);
      sassert(1 <= j);
      sassert(j <= n);
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      sassert(1 <= l);sassert(l <= n);
      l--;
    } else {
      sassert(1 <= r);sassert(r <= n);
      r--;
    }
  }
  sassert(l==1);
  }
  return 0;
}

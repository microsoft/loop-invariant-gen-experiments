#include "seahorn/seahorn.h"

extern int unknown();

int main( int argc, char *argv[]){
  int n,l,r,i,j;
  n = unknown();
  l = unknown();

  //tmpl("(le(n,l,r,i,j),le(n,l,r,i,j),le(n,l,r,i,j))");
  //tmpl("(le(n,l,r,i,j),le(n,l,r,i,j))");
  
  if(1 <= n && n == 2 * (l-1)) {
  //l = n/2 + 1;
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
	sassert(1 <= j);
	sassert(j <= n);
	sassert(1 <= j+1); sassert(j+1 <= n);
	if( unknown() )
	  j = j + 1;
      }
      sassert(1 <= j); sassert(j <= n);
      /*      if( unknown() ) { 
      	break;
	}
      */
      sassert(1 <= i);
      sassert(i <= n);
      sassert(1 <= j);
      sassert(j <= n);
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      sassert(1 <= l); sassert(l <= n);
      l--;
    } else {
      sassert(1 <= r); sassert(r <= n);
      r--;
    }
  }
  }
  return 0;
}


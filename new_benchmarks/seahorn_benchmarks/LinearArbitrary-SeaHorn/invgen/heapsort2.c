#include "seahorn/seahorn.h"

extern int unknown();

int main( int argc, char *argv[]){
  int n,l,r,i,j;
  n = unknown();
  l = unknown();

  //tmpl("(le(n,l,r,i,j),le(n,l,r,i,j),le(n,l,r,i,j))");
  //tmpl("(le(n,l,r,i,j),le(n,l,r,i,j))");
  
  if(1 <= n && n == 2 * (l - 1)) {
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
	if( unknown() )
	  j = j + 1;
      }
      if( unknown() ) { 
      	break;
      }
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      sassert(l <= n);
      l--;
    } else {
      r--;
    }
  }
  }
  return 0;
}


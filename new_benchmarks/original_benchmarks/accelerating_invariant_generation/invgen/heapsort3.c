#include "myassert.h"

int NONDET;

int main( int argc, char *argv[]){
  int n,l,r,i,j;

  //tmpl("(le(n,l,r,i,j),le(n,l,r,i,j),le(n,l,r,i,j))");
  tmpl("(le(n,l,r,i,j),le(n,l,r,i,j))");
  
  assume(1 <= n);
  l = n/2 + 1;
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
	__VERIFIER_assert(1 <= j);
	assume(j <= n);
	assume(1 <= j+1);assume(j+1 <= n);
	if( NONDET )
	  j = j + 1;
      }
      assume(1 <= j);assume(j <= n);
      /*      if( NONDET ) { 
      	break;
	}
      */
      assume(1 <= i);
      assume(i <= n);
      assume(1 <= j);
      assume(j <= n);
      i = j;
      j = 2*j;
    }
    if(l > 1) {
      assume(1 <= l);assume(l <= n);
      l--;
    } else {
      assume(1 <= r);assume(r <= n);
      r--;
    }
  }
  return 0;
}


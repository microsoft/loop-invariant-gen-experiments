#include "myassert.h"

void main() {
  int n0, n1;
  int i0 = 0;
  int k = 0;

  while( i0 < n0 ) {
    tmpl("(le(n0,n1,i0,i1,j1,k),le(n0,n1,i0,i1,j1,k))");
    i0++;
    k++;
  }
  int i1 = 0;
  while( i1 < n1 ) {
    tmpl("(le(n0,n1,i0,i1,j1,k),le(n0,n1,i0,i1,j1,k))");
    i1++;
    k++;
  }
  int j1 = 0;
  while( j1 < n0 + n1 ) {
    tmpl("(le(n0,n1,i0,i1,j1,k),le(n0,n1,i0,i1,j1,k))");
    if(k <= 0) __VERIFIER_assert(0);    
    j1++;
    k--;
  }
}

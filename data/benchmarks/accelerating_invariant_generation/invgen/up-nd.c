#include "myassert.h"

void main() {
  int n, v;
  int i = 0;
  int k = 0;
  while( i < n ) {
    tmpl("(le(v,i,j,k,n),le(v,i,j,k,n))");
	i++;
	v = rand();
	if( v > 0 )
	  k = k + v;
	else
	  k++;
  }
  int j = 0;
  while( j < n ) {
    tmpl("(le(v,i,j,k,n),le(v,i,j,k,n))");
	if(k <= 0) __VERIFIER_assert(0);
	j++;
	k--;
  }
}

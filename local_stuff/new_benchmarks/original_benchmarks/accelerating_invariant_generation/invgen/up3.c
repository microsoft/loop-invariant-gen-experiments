#include "myassert.h"

void main() {
  int n;
  int i = 0;
  int k = 0;
  while( i < n ) {
   tmpl("(le(i,j,k,n),le(i,j,k,n))");
	i = i + 2;
	k++;
  }
  int j = 0;
  while( j < n ) {
   tmpl("(le(i,j,k,n),le(i,j,k,n))");
    if(k <= 0) __VERIFIER_assert(0);
	j = j + 2;
	k--;
  }
}

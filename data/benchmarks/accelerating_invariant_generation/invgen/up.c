#include "myassert.h"

void main() {
  int n;
  int i = 0;
  int k = 0;
  tmpl("(le(i,j,k,n),le(i,j,k,n))");
  while( i < n ) {
	i++;
	k++;
  }
  int j = 0;
  while( j < n ) {
    __VERIFIER_assert(k > 0);
    j++;
    k--;
  }
}

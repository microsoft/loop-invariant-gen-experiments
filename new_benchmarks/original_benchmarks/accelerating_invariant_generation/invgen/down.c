#include "myassert.h"

void main() {
  int n;
  int k = 0;
  int i = 0;
  tmpl("(le(i,j,k,n),le(i,j,k,n))");
  while( i < n ) {
	i++;
	k++;
  }
  int j = n;
  while( j > 0 ) {
	__VERIFIER_assert(k > 0);
	j--;
	k--;
  }
}

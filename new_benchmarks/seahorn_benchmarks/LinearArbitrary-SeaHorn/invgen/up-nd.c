#include "seahorn/seahorn.h"

void main() {
  int n, v;
  n = unknown();
  int i = 0;
  int k = 0;
  while( i < n ) {
	i++;
	v = unknown();
	if( v > 0 )
	  k = k + v;
	else
	  k++;
  }
  int j = 0;
  while( j < n ) {
	if(k <= 0) sassert(0);
	j++;
	k--;
  }
}

#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int n = unknown();
  int k = 0;
  int i = 0;
  while( i < n ) {
	i++;
	k++;
  }
  int j = n;
  while( j > 0 ) {
	sassert(k > 0);
	j--;
	k--;
  }
}

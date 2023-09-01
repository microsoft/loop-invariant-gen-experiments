#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int n = unknown();
  int i = 0;
  int k = 0;
  while( i < n ) {
	i++;
	k++;
  }
  int j = 0;
  while( j < n ) {
    sassert (k > 0);
    j++;
    k--;
  }
}

#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int n = unknown();
  int i = 0;
  int k = 0;
  while( i < n ) {
	i++;
	k = k + 2;
  }
  int j = 0;
  while( j < n ) {
    if(k <= 0) sassert(0);
	j = j + 2;
	k--;
  }
}

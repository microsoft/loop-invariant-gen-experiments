#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int n,j,i,k;

  i = 0;
  k = 0;
  j = unknown();
  n = unknown();

  if ( j<=n ) {
  while ( j <= n ) {
    //assume( i >= 0);
    j++;
  }
  sassert( i>= 0);
  }
}

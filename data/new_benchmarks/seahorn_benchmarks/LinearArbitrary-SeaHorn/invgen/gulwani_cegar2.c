#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int x,m,n;
  n = unknown();
  x = 0;
  m = 0;
  while( x < n ) {
    if(unknown())
	m = x;
	x++;
  }
  if( n > 0 )
    {
      sassert( 0<=m);
      sassert(m<n);
    }
}

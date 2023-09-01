
#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */


void main() {
  int i,j,k,n,m;
  i = unknown1();
  j = unknown1();
  k = unknown1();
  n = unknown1();
  m = unknown1();
  if( m+1 < n ); else return;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if (unknown1()){
        sassert( j >= 0 );
        j++;
        k = 0;
        while( k < j ) {
          k++;
        }
      }
      else { 
	sassert( n+j+5>i );
	j+= 2;
      }
    }
  }
}

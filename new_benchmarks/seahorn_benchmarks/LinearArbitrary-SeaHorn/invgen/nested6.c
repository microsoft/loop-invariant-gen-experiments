#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int i,j,k,n;
  k = unknown();
  n = unknown();

  if( k == n); else goto END;

  for (i=0;i<n;i++) {
    for (j=2*i;j<n;j++) {
      if( unknown() ) {
	for (k=j;k<n;k++) {
	  sassert(k>=2*i);
	}
      }
      else {
	sassert( k >= n );
	sassert( k <= n );
      }
    }
  }
 END:;
}

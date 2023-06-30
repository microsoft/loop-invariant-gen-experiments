#include "seahorn/seahorn.h"

extern int unknown1 ();
extern int unknown2 ();

/*
 * From "Path Invariants" PLDI 07 by Beyer et al.
 */

int main() {
  int i, n, a, b;
  n = unknown1 ();
  i = 0; a = 0; b = 0;

  /*int m = unknown1();
  int n = unknown1();
  
  int size = m;
  int copy = n;
  while (size > 0) {
    int vail = unknown1 ();
    if (vail > size) {
       copy += vail;
       size -= vail;
    }
  }
   
    sassert ( size != 0 || copy == m+n );*/
  


  if (n >= 0) {
  	while( i < n ) {
    		if(unknown2()) {
      			a = a+1;
      			b = b+2;
    		} else {
      			a = a+2;
      			b = b+1;
    		}
    		i = i+1;
  	}
  	sassert( a+b == 3*n );
  }

  return 0;
}

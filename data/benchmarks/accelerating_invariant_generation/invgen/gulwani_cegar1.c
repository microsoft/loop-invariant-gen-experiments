#include "myassert.h"

int __BLAST_NONDET;
void main() {
  int x,y;

  assume(0 <= x);  assume(x <= 2);
  assume(0 <= y);  assume(y <= 2);
  while( __BLAST_NONDET ) {
	x+=2;
	y+=2;
  }
  if( y >= 0 ) 
    if( y <= 0 ) 
      if( 4 <= x ) 
	__VERIFIER_assert( x < 4 );
}

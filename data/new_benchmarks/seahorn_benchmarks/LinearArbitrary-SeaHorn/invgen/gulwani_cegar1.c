#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int x = unknown();
  int y = unknown();

  assume(0 <= x);  assume(x <= 2);
  assume(0 <= y);  assume(y <= 2);

  if (x >= 0 && x <= 2 && y >= 0 && y <= 2) {
  while( unknown() ) {
	x+=2;
	y+=2;
  }
  if( y >= 0 ) 
    if( y <= 0 ) 
      if( 4 <= x ) 
	sassert( x < 4 );
  }
}

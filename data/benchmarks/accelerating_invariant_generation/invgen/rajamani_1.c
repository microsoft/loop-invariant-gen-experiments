#include "myassert.h"
int __BLAST_NONDET;

int main(){
  int x=0;
  int y=0;
  int z=0;
  int w=0;

  while ( __BLAST_NONDET ){
    if ( __BLAST_NONDET ) {
      x++; y = y+100;
    } else if  ( __BLAST_NONDET ) {
      if( x >= 4)
	{ x=x+1; y=y+1;}
    } else if  ( y >10*w)
      if (z>=100*x )
      y = -y;
    w=w+1; 
    z=z+10;
  }
  if ( x >=4 )
    __VERIFIER_assert(y>2);
}

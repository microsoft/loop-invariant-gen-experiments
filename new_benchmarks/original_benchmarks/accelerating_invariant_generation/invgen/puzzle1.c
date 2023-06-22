#include<stdio.h>
#include "myassert.h"

int main(){
  //int x1 = 1,x2 = -1 ,x3 = -2,x4 = 3,x5 = 2;
  int x1,x2 ,x3,x4,x5;

  if (x1+x2+x3+x4+x5 >0); else goto END;

Loop:
  
  if( x1 < 0 ) { x1 = -x1; x5 = x5-x1; x2 = x2-x1; }
  else if( x2 < 0 ) { x2 = -x2; x1 = x1-x2; x3 = x3-x2; } 
  else if( x3 < 0 ) { x3 = -x3; x2 = x2-x3; x4 = x4-x3; }
  else if( x4 < 0 ) { x4 = -x4; x3 = x3-x4; x5 = x5-x4; }
  else if( x5 < 0 ) { x5 = -x5; x4 = x4-x5; x1 = x1-x5; }
  else goto END;

  //printf("%d %d %d %d %d \n", x1, x2, x3, x4, x5);getchar();

  goto Loop;

END:
  return 1;
}

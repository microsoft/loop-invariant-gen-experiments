#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();

/*
 * Based on ex16 from NECLA Static Analysis Benchmarks
 */


int main()
{
  int x = unknown1();
  int y = unknown2();
  int i=0;
  int t=y;
   
  if (x==y) return x;
  
  while (unknown3()){
    if (x > 0)   
      y = y + x;
  }
   
 
  sassert(y>=t);
	
}



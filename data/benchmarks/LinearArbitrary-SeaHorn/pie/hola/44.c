#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * Adapted from ex20 from NECLA Static Analysis Benchmarks
 */


int main()
{
  int k = unknown1();
  int flag = unknown1();
  int i=0;
  int j=0;
  int n = unknown1();


  if (flag == 1){
     n=1;
  } else {
     n=2;
  }

  i=0;

  while ( i <= k){
    i++;
    j= j +n;
  }
  if(flag == 1)
      sassert(j == i);
	
}



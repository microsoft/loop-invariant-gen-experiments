#include "seahorn/seahorn.h"
extern int unknown();

void main()
{
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  int n = unknown();
  
 
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  

  if(i==m) sassert(x==2*y);
}


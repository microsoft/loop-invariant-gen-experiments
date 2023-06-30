#include "seahorn/seahorn.h"

extern int unknown1();

void main()
{
    int x, y, k, j, i, n;
    x = unknown1();
    y = unknown1();
    k = unknown1();
    j = unknown1();
    i = unknown1();
    n = unknown1();
    if((x+y)== k) {
    int m = 0;
    j = 0;
    while(j<n) {
      if(j==i)
      {
         x++;
         y--;
      }else
      {
         y++;
         x--;
      }
	if(unknown1())
  		m = j;
      j++;
    }
    sassert((x+y)== k);
    if(n>0)
    {
   	sassert (0<=m); 
	sassert (m<n);
    }
    }
}


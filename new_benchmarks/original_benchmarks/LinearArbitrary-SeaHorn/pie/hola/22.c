#include "seahorn/seahorn.h"
extern int unknown1();

void main()
{
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  while(unknown1())
  {
     if(k%3 == 0)
       x++;
     y++;
     z++;
     k = x+y+z;
  }

  sassert(x==y && y==z); 
}


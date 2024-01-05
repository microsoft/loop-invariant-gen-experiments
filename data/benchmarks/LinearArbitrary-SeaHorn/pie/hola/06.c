#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();

void main()
{
  int w = 1;
  int z = 0;
  int x= 0;
  int y=0;

  while(unknown1()){
	  
    while(unknown2()){
      if(w%2 == 1) x++;
      if(z%2==0) y++;
    }
    z=x+y;
    w=z+1;
  }

  
  sassert(x==y);
}

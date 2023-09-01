#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

void main()
{
  int w=1, z=0, x=0, y=0;
  while(unknown1()){
    while(unknown2()){
      if(w%2 == 1) 
        x++;
      if(z%2==0)
        y++;
    }
    while(unknown4())
    {
      z=x+y;
      w=z+1;
    }
  }
  sassert(x==y);
}

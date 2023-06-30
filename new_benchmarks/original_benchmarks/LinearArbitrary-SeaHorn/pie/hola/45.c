#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

void main()
{	
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;
  int c = 0;
  int d = 1;
  int flag = unknown4();
  while(unknown1())
  {
    x++;
    y++;
    i+=x;
    j+=y;
    if(flag) 
    {
      j+=1;
    }
  } 
  if(j>=i)
    x=y;
  else
    x=y+1;

  int w = 1;
  int z = 0;
  while(unknown2()){
    while(unknown3()){
      if(w%2 == 1) 
        x++;
      if(z%2==0)
        y++;
      }
      z=x+y;
      w=z+1;
  }
  sassert(x==y);
}

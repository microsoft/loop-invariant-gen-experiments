#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

int main()
{
  int k = unknown4();
  int z = k;
  int x = 0;
  int y = 0;

  while(unknown1())
  {
    int c = 0;
    while(unknown2())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
    while(unknown3())
    {
      x--;
      y--;
    }
    z=k+y;
  }
  sassert(x==y);
}

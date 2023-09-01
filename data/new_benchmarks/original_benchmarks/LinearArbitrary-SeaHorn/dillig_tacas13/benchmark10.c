#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

int main(int k)
{
  int z = k;

  int i = 900;
  int j = 20;
  while(j > 0)
  {
     i--;
     j--;
   }
  int x = j;
  int y = j;

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

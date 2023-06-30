#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();

int main()
{
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
  while(unknown1())
  {
    x = a+c;
    y = b+d;
    if((x+y)%2 == 0)
    {
      a++;
      d++;
    }else
    {
      a--;
    }
    while(unknown2())
    {
       c--;
       b--;
    }
  }
  sassert(a+c==b+d);
}

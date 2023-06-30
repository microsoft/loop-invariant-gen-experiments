#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();

void main()
{
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  while(unknown1())
  {
    while(unknown2())
    {
       if(x==y)
          i++;
       else
          j++;
    }
    if(i>=j)
    {
       x++;
       y++;
    }
    else
       y++;
  }

  sassert(i>=j);
}

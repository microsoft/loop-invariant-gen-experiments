#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();
extern int unknown3();


int main(int flag)
{
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  
  int s = 1;
  int t = 0;
  int j = 1;

  int k = 1;
  int w = 0;

  int x;
  int y = 3;

  while(unknown3())
  {
		j = s-t;
    s++;
    t++;
    c++;   
    d = d+k-w;
  }

 	

  if(j%2 == 1)
      x = 3;
  else
      x = 2;

	
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

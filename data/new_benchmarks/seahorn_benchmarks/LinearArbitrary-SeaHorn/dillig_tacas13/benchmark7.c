/*
 * benchmark 7
 */

#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();

void main(int flag)
{

	int x = 0;
	int y = 0;
	int a;


	if(flag)
		a = 0;
	else
 		a = 1;

	int z;
  while(unknown2())
	{
		z=y-x;
		a+=z;
		x++;
		y++;
	}

	x=1; 
	y=1;	
  while(unknown1()){
			if(flag)
			{
					a = x+y;
					x++;
			}
			else
			{
					a = x+y+1;
					y++;
			}
			if(a%2==1)
				y++;
			else
				x++;	  
  }
	//x==y

  if(flag)
			a++;
  int t = a%2;
  sassert(t==1);
}

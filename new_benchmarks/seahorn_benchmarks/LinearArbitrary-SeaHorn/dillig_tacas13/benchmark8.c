/*
 * benchmark 8
 */
#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


void main()
{
	int flag = unknown1();
	int j = 0;
	int i = 0;
	int a = 0;
  int b = 0;

	while(unknown1())
	{
		a++;
    b++;
		i+=a;
		j+=b;
		if(flag) 
		{
			j+=1;
		}
	} 
	

	int x = 1;
	if(flag)  
	{
		x = i-j+2;
	}


	int y = 0;
	while(y<=x) 
	{
   if(unknown2()) 
			y++;
   else 
			y+=2;
	}
  sassert(y<=4);
}

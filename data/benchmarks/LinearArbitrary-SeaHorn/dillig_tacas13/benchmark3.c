/*
 * benchmark 3
 */

#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();


void main()
{
	int a=0;
	int b=0;

	while(unknown1()) 
	{
  	a = b+1;
  	b= b+a;
  	if(a%2 ==0) 
		{
    	b+=1;
  	}
 	}

	int x = 0;
	int y = 0;

 	while(unknown2()) {
  	y+=a;
   	if(x%2==0) 
			y++;
   	if(y%2==0) 
			x+=b-a;
   	else 
			x+=a;
 	}

	a=1;
	b=2;

	while(unknown3())
	{
		y+=b;
		x+=a;
		a++;
 		b++;
	}

	sassert(y>=x);
}

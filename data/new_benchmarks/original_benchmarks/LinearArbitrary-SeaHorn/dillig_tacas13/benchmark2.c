/*
 * benchmark 2
 */
#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


int main()
{
	int i = 1;
	int j = 0;
	while(unknown1()) 
	{
		j++;
		i+=3;
	}
	//(i-j)%2=1

	int z = i-j;
	int x = 0;
	int y = 0;
	int w = 0;

	while(unknown2()) 
	{
		z+=x+y+w;
		y++;
		if(z%2==1) 
			x++;
		w+=2; 
	}
	//x==y && z%2==1 && w%2==0

	sassert(x==y);
}

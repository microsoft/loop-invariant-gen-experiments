/*
 * benchmark 5
 */

#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();
extern int unknown3();
extern int unknown4();

void main(int flag)
{
	int a = 0;
  int b = 0;
	int x = 0;
	int y = 0;
	int z = 0;
	

	int i = 1000, j = 10;
  while(j > 0){
    i--;
    j--;
  }

	//w = j = 0
  int w = j; 

	while(unknown1())
	{
		int i = z;
		int j = w;
		int k = 0;

		while(i<j)
		{
			k++;
			i++;
		}

		x = z;
		y = k;

		if(x%2==1)
		{
			x++;
			y--;
		}

		while(unknown2()) 
		{
			if(x%2==0)
			{
				x+=2;
				y-=2;
			}
			else
			{
				x--;
				y--;
			}
		}
		z++;
		w = x+y+1;
		if(unknown3()) 
			w+=1;
	}

  int c=0; 
  int d=0;
 	while(unknown4())
	{
    c++;
    d++;
		if(flag)
		{
			a++;
			b++;
		}
		else
		{
			a+=c;
			b+=d;
		}
	}

	sassert(w>=z && a-b==0 && i > 10);

}

/*
 * benchmark 6
 */

#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();

void main()
{

	int i=0;
	int j=0;
	int a=0;
	int b=1;
  	int c=0;
	int d=2;

	while(unknown3())
	{
		i+=b-a;
		j+=d-c;
		d++;
		c++;
		a+=2;
		b+=2;
	}

  int x;
  int y;

  if(j%2==1) 
		x=1;
  else 
		x=0;
	
  y=0;
  i=2;
  j=1;

  while(unknown1()){
      y++;
			if(a%2==0)
				x++;
			else
				x+=2;
      while(unknown2()){
				j = y;
				if(a%2==1)
					i = x;
				else
					i = j + x;	  
		  }
      a = i;
  }
	//i=2j& x=y& a%2=0
	
  sassert(x==y);
}




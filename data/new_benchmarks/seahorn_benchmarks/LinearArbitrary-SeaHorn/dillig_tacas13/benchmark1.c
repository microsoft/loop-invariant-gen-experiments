/*
 * benchmark 1
 */

#include "seahorn/seahorn.h"

extern int unknown1();
extern int unknown2();


void main()
{
	int flag = unknown1();

	int t = 0;
	int s = 0;
	int a = 0;
  	int b = 0;

	
	while(unknown1()){
		a++;
    		b++;
		s+=a;
		t+=b;
		if(flag){
			t+=a;
		}
	} 
	//2s >= t
	

	int x = 1;
	if(flag){
		x = t-2*s+2;
	}
	//x <= 2

	int y = 0;
	while(y<=x){
   		if(unknown2()) 
			y++;
   		else 
			y+=2;
	}
  	sassert(y<=4);
}

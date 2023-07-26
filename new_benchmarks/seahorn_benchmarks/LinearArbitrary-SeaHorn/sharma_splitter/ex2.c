#include "seahorn/seahorn.h"

int main() {
	int x, y, z;
	x=0;y=0;z=0;
	while (x<100) {
		if(x<=50)
               		y=y+1;
       		else
               		y=y-1;
       
       		if(x<25)
               		z=z+1;
       		else
               		z=z+5;
       
       		x=x+1;
	}
	sassert(z==400);
	sassert(y==2);
	sassert(x==100);
	return 0;
}
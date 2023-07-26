#include "seahorn/seahorn.h"
extern int unknown2();

void main() {


	int w = 1;
	int z = 0;
	int x= 0;
	int y=0;

 
         while(unknown2()){
	    if(w) {
		x++; 
		w=!w;
	    };
	    if(!z) {
		y++; 
		z=!z;
	    };
	}

  
	sassert(x==y);
  
}

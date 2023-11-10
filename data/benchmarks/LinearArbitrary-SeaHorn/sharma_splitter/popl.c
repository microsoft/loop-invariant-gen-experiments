#include "seahorn/seahorn.h"

int main(){
       int x, y;
       x=0;
       y=50;
       while(x<100) {
               x=x+1;
               if (x>50) {
                       y=y+1;
               }
       }
	sassert(y==100);
	return 0;
}
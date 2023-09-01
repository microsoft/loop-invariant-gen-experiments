#include "seahorn/seahorn.h"

int main(){
       int x, y, flag;
       x=0;
       y=0;
       flag=0;
       while (flag < 1) {
               if (x<=50)
                       y=y+1;
               else
                       y=y-1;
               
               if (y<0) {
                       flag=1;
               }
               if (flag < 1) {
                       x=x+1;
               }
       }

	sassert(x<=102);
	sassert(y<=51);
	return 0;
}
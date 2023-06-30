#include "seahorn/seahorn.h"
extern int unknown1();
extern int unknown2();
extern int unknown3();

/*
 *  Based on "Automatically refining abstract interpretations" fig.1
 */


void main() {
 int x = 0, y = 0;
 while(unknown1()){
   if(unknown2()){ 
      x++; 
      y+=100; 
   }
   else if (unknown3()){ 
      if (x >= 4) { 
          x++; 
          y++; 
      } 
      if (x < 0){
          y = -y;
      }
   }
  
 }
 sassert(x < 4 || y > 2);
}

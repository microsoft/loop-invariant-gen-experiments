#include "seahorn/seahorn.h"
extern int unknown1();

/*
 * From "The Octagon Abstract Domain" HOSC 2006 by Mine.
 */

int main() {
  int a = 0;
  int j = unknown1();
  int m = unknown1();
  if(m<=0)
    return 0;
  for(j = 1; j <= m ; j++){
    if(unknown1()) 
       a++;
    else
       a--; 
  }
  sassert(a>=-m && a<=m);
}

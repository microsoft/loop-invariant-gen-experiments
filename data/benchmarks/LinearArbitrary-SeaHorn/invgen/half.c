//#include <stdio.h>
#include "seahorn/seahorn.h"

extern int unknown();

int main(int argc, char** argv) {
  int n,i,k;
  n = unknown(); 
  i = unknown();
  k = unknown(); 

  k = n;
  i = 0;
  while( i < n ) {
    k--;
    i = i + 2;
  }

  int j = 0;
 
  while( 2*j < n ) {
    sassert(k >= 0);
    k--;
    j++;
  }

  return 0;
}

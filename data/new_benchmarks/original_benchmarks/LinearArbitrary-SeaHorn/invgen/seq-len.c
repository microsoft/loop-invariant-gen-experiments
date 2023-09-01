#include "seahorn/seahorn.h"

extern int unknown1();

int main(int argc, char *argv[]) {
  int n0, n1, n2;
  int i = 0;
  int k = 0;
  n0 = unknown1();
  n1 = unknown1();
  n2 = unknown1();
 
  if (n0 > 0 && n1 > 0 && n2 > 0) {
  while( i < n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < n1 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k++;
  }

  i = 0;
  while( i < n2 ) {
    i++;
    k--;
  }

  i = 0;
  while( i < n1 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n0 ) {
    sassert(k > 0);
    i++;
    k--;
  }
  }
  return 0;
}

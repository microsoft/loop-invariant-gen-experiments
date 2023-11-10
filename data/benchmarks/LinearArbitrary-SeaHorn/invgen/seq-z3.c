
#include "seahorn/seahorn.h"

extern int unknown();

int main() {
  int n0, n1;
  int i = 0;
  int k = 0;
  n0 = unknown();
  n1 = unknown();

  while( i < 20*n0 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k++;
  }
  i = 0;
  while( i < 6*n1+128 ) {
    i++;
    k--;
  }
  i = 0;
  while( i < 20*n0 ) {
    sassert(k > 0);
    i++;
    k--;
  }
  return 0;
}

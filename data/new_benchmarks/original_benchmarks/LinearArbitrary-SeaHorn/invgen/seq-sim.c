
#include "seahorn/seahorn.h"

int main() {
  int n, m;
  int i = 0;
  int k = 0;
  n = unknown();
  m = unknown();

  while( i < n ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k++;
  }
  i = 0;
  while( i < m ) {
    i++;
    k--;
  }
  i = 0;
  while( i < n ) {
    sassert(k > 0);
    i++;
    k--;
  }
  return 0;
}

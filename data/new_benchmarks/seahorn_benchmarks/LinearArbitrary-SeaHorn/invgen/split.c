#include "seahorn/seahorn.h"

extern int unknown();

void main() {
  int k = 100;
  int b = 0;
  int i;
  int j;
  int n;
  i = j = 0;
  for( n = 0 ; n < 2*k ; n++ ) {
    //tmpl("(le(k,b,i,j,n),le(k,b,i,j,n))");    
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
  sassert(i == j);
}

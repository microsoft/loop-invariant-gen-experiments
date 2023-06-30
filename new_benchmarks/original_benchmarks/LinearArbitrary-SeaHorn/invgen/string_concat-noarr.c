#include "seahorn/seahorn.h"

extern int unknown();

int main(void) {
  int i, j;
  //tmpl("(le(i,j),le(i,j))");
 L0:
  i = 0;
 L1:
  while( unknown() ){
  //tmpl("(le(i,j),le(i,j))");
    i++;
  }
  if(i >= 100) STUCK: goto STUCK; //  assume( i < 100 );
  j = 0;
 L2:
  while( unknown() ){
    //tmpl("(le(i,j),le(i,j))");
    i++;
    j++;
  }
  if(j >= 100) goto STUCK; // assume( j < 100 );
  sassert( i < 200 ); /* prove we don't overflow z */
  return 0;
}

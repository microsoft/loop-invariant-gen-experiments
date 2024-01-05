#include "myassert.h"

int NONDET;

int main() {
  int i, j;
  tmpl("(le(i,j),le(i,j))");
 L0:
  i = 0;
 L1:
  while( NONDET ){
  tmpl("(le(i,j),le(i,j))");
    i++;
  }
  if(i >= 100) STUCK: goto STUCK; //  assume( i < 100 );
  j = 0;
 L2:
  while( NONDET ){
    tmpl("(le(i,j),le(i,j))");
    i++;
    j++;
  }
  if(j >= 100) goto STUCK; // assume( j < 100 );
  __VERIFIER_assert( i < 200 ); /* prove we don't overflow z */
  return 0;
}

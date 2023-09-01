#include "myassert.h"

int main(int argc, char *argv[]) {
  int n0, n1,n2;
  int i = 0;
  int k = 0;

  tmpl("(le(n0,n1,i,k),le(n0,n1,i,k))");

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
    __VERIFIER_assert(k > 0);
    i++;
    k--;
  }
  return 0;
}

#include "myassert.h"

int nondet_int();

int n0, n1;

int main(){
 
  n0 = nondet_int();
  n1 = nondet_int();

  int i0 = 0;
  int k = 0;

  tmpl("2");
  while( i0 < n0 ) {
    i0++;
    k++;
  }
  int i1 = 0;
  while( i1 < n1 ) {
    i1++;
    k++;
  }
  int j1 = 0;
  while( j1 < n1 ) {
    if(k <= 0) __VERIFIER_assert(0);
    j1++;
    k--;
  }
  int j0 = 0;
  while( j0 < n0 ) {
    if(k <= 0) __VERIFIER_assert(0);
    j0++;
    k--;
  }
  return 0;
}

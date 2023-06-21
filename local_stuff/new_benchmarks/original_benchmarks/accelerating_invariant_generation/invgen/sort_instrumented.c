#include "myassert.h"



int __BLAST_NONDET;

int heap_size, k_buffer, k_c;
/*
bound_var(data(V1, V6, V4, V5, V2, V3),V2).
bounding_vars(data(V1, V6, V4, V5, V2, V3),[V1]).
*/

int n;
int nondet_int();

void main() {
  n = nondet_int();
  int k;
  //n = 30;
  bound_var(heap_size);
  bounding_var(n);

  assume( n > 0);
  heap_size = 0;
  while ( __BLAST_NONDET ) {

    k_buffer = 0;
    for (k=0;k<n;k++) {
      k_buffer++;
      heap_size++;
    }

    k_c = k_buffer;
    while( __BLAST_NONDET ) {
      assume(k_c > 0);
      k_c--;
      heap_size--;
    }
    assume( k_c == 0);
  }
}

//void main() {
//  sort(30);
//}

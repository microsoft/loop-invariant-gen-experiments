#include "seahorn/seahorn.h"

/*
bound_var(data(V1, V6, V4, V5, V2, V3),V2).
bounding_vars(data(V1, V6, V4, V5, V2, V3),[V1]).
*/
void main() {
  int k, n;
  
  int heap_size, k_buffer, k_c;
  n = unknown();
  __VERIFIER_assume( n > 0);
  heap_size = 0;
  while ( unknown() ) {

    k_buffer = 0;
    for (k=0;k<n;k++) {
      k_buffer++;
      heap_size++;
    }

    k_c = k_buffer;
    while( k_c > 0 ) {
      k_c--;
      heap_size--;
    }
    sassert( heap_size == 0);
  }
}

//void main() {
//  sort(30);
//}

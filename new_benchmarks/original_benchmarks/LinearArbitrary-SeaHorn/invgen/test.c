#include "seahorn/seahorn.h"

void main() {
  int n,h;
  int i,j,k,m;

  __VERIFIER_assume(n >=0 );
  __VERIFIER_assume(n <=200); 
}
/*
bound_vars(vars(n)).

bound_exp(pc(main-1-11), i+k).
bound_exp(pc(main-10-18),j+m).

bound_var(data(V1, V5, V2, V4, V3),V4).
bounding_vars(data(V1, V5, V2, V4, V3),[V1]).

*/

#include "myassert.h"


void main() {
  int i,k,n,l;

  tmpl("(le(n,i,k,l),le(n,i,k,l))");

  assume(l>0);

  for (k=1;k<n;k++){
    //__VERIFIER_assert(k<=n);
    //__VERIFIER_assert(1<=k)__VERIFIER_assert(1<=j);;
    for (i=l;i<n;i++) {
      __VERIFIER_assert(1<=k);
      //__VERIFIER_assert(1<=i);
      //__VERIFIER_assert(i<=n);
    }
    for (i=l;i<n;i++) {

    }
  }

 }

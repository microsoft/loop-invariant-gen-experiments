 #include "myassert.h"


void main() {
  int i,k,n,l;

  tmpl("(le(n,i,k),le(n,i,k))");

  for (k=1;k<n;k++){
    //    __VERIFIER_assert(k<=n);
    //   __VERIFIER_assert(1<=k);
    for (i=1;i<n;i++) {
      //__VERIFIER_assert(1<=k);
      // __VERIFIER_assert(1<=i);
      // __VERIFIER_assert(i<=n);
    }
  }
  __VERIFIER_assert(1<=k);
 }

#include "seahorn/seahorn.h"

void main() {
  int i,k,n,l;

  //tmpl("(le(n,i,k,l),le(n,i,k,l))");

  //assume(l>0);
  n = unknown ();
  l = unknown ();
  k = unknown ();
  i = unknown ();
  if (l > 0) {
  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {
    }
    for (i=l;i<n;i++) {
      sassert(1<=i);
    }
  }
  }
 }

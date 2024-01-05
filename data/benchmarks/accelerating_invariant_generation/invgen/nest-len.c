 #include "myassert.h"


void main() {
  int i,k,n,l;

  tmpl("(le(n,i,k))");

  //assume(l>0);

  for (k=1;k<n;k++){
    __VERIFIER_assert(1<=k);
    for (i=1;i<n;i++);  
    for (i=1;i<n;i++);
    for (i=1;i<n;i++);
    for (i=1;i<n;i++);
    for (i=1;i<n;i++);
    for (i=1;i<n;i++);
    for (i=1;i<n;i++);
  }

 }

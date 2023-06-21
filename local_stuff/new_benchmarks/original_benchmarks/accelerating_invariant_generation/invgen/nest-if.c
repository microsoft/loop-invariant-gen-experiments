 #include "myassert.h"


void main() {
  int i,k,n;

  //  tmpl("(le(n,i,k,l),le(n,i,k,l))");
  tmpl("(le(n,i,k),le(n,i,k))");

  //  assume(l>0);

  for (k=1;k<n;k++){
    for (i=1;i<n;i++)
      __VERIFIER_assert(1<=k);
    if(i<n)
      for (i=1;i<n;i++);
  }

 }

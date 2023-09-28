 #include "myassert.h"

int NONDET;

void main() {
  int i,k,n,l;

  tmpl("(le(n,i,k,l),le(n,i,k,l))");

  assume(l>0);

  for (k=1;k<n;k++){
    for (i=l;i<n;i++)
      __VERIFIER_assert(1<=i);
    if(NONDET)
      for (i=l;i<n;i++);
  }
  
}
